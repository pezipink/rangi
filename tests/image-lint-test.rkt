#lang racket/base
; L5 structural invariants: every fixture image lints clean, and damaged copies are reported
(require rackunit racket/file "lib/fixture.rkt" "lib/pe-lint.rkt")

(define (le-at bs pos n)
  (for/fold ([acc 0]) ([i (in-range n)])
    (+ acc (arithmetic-shift (bytes-ref bs (+ pos i)) (* 8 i)))))

(define (poke! bs pos n v)
  (for ([i (in-range n)])
    (bytes-set! bs (+ pos i) (bitwise-and (arithmetic-shift v (* -8 i)) 255))))

; position of an optional header field, given its offset from the start of the optional header
(define (opt-pos bs off) (+ (le-at bs #x3C 4) 24 off))

(define (file-offset bs rva)
  (define lfanew (le-at bs #x3C 4))
  (define nsec (le-at bs (+ lfanew 6) 2))
  (define sec0 (+ lfanew 24 (le-at bs (+ lfanew 20) 2)))
  (or (for/or ([i (in-range nsec)])
        (define s (+ sec0 (* 40 i)))
        (define va (le-at bs (+ s 12) 4))
        (define vsize (le-at bs (+ s 8) 4))
        (and (<= va rva) (< rva (+ va vsize)) (+ (le-at bs (+ s 20) 4) (- rva va))))
      (error 'file-offset "no section holds RVA ~x" rva)))

; applies damage to a copy of the image and returns what the lint reports for it
(define (lint-damaged exe damage!)
  (define bs (file->bytes exe))
  (damage! bs)
  (define copy (make-temporary-file "rangi-lint-~a.exe"))
  (dynamic-wind
   void
   (λ ()
     (call-with-output-file copy (λ (out) (write-bytes bs out)) #:exists 'truncate)
     (lint-image copy))
   (λ () (delete-file copy))))

(define (reports? problems rx)
  (ormap (λ (p) (regexp-match? rx p)) problems))

(for ([name (fixture-names)])
  (test-case (format "~a image passes the L5 lint" name)
    (with-built-image name
      (λ (dir exe)
        (check-equal? (lint-image exe) '())))))

(with-built-image
 "nano"
 (λ (dir exe)
   (test-case "SizeOfImage that does not end at the last section is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define pos (opt-pos bs 56))
                           (poke! bs pos 4 (+ (le-at bs pos 4) #x1000)))))
     (check-true (reports? problems #rx"SizeOfImage")))

   (test-case "CLI header without the ILONLY flag is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define cli-rva (le-at bs (opt-pos bs (+ 96 (* 8 14))) 4))
                           (define pos (+ (file-offset bs cli-rva) 16))
                           (poke! bs pos 4 (bitwise-and (le-at bs pos 4) (bitwise-not 1))))))
     (check-true (reports? problems #rx"ILONLY")))

   (test-case "entry stub that does not jump through the import table is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define entry (le-at bs (opt-pos bs 16) 4))
                           (define pos (+ (file-offset bs entry) 2))
                           (poke! bs pos 4 (+ (le-at bs pos 4) 4)))))
     (check-true (reports? problems #rx"import address table")))

   (test-case "metadata root without the BSJB signature is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define cli-rva (le-at bs (opt-pos bs (+ 96 (* 8 14))) 4))
                           (define md-rva (le-at bs (+ (file-offset bs cli-rva) 8) 4))
                           (bytes-set! bs (file-offset bs md-rva) (char->integer #\X)))))
     (check-true (reports? problems #rx"BSJB")))

   (test-case "DOS header without the MZ magic is reported"
     (define problems
       (lint-damaged exe (λ (bs) (bytes-set! bs 0 (char->integer #\X)))))
     (check-true (reports? problems #rx"MZ")))

   (test-case "COFF characteristics without EXECUTABLE_IMAGE are reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define pos (+ (le-at bs #x3C 4) 22))
                           (poke! bs pos 2 (bitwise-and (le-at bs pos 2) (bitwise-not 2))))))
     (check-true (reports? problems #rx"EXECUTABLE_IMAGE")))

   (test-case "Subsystem 0 is reported"
     (define problems
       (lint-damaged exe (λ (bs) (poke! bs (opt-pos bs 68) 2 0))))
     (check-true (reports? problems #rx"Subsystem")))

   (test-case "RELOCS_STRIPPED with a base relocation directory present is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define pos (+ (le-at bs #x3C 4) 22))
                           (poke! bs pos 2 (bitwise-ior (le-at bs pos 2) 1)))))
     (check-true (reports? problems #rx"stripped")))

   (test-case "entry section without execute permission is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           ; .text is the first section header, its Characteristics at +36
                           (define pos (+ (le-at bs #x3C 4) 24 224 36))
                           (poke! bs pos 4 (bitwise-and (le-at bs pos 4) (bitwise-not #x20000000))))))
     (check-true (reports? problems #rx"readable and executable")))

   (test-case "section without read permission is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           ; .reloc is the second section header
                           (define pos (+ (le-at bs #x3C 4) 24 224 40 36))
                           (poke! bs pos 4 (bitwise-and (le-at bs pos 4) (bitwise-not #x40000000))))))
     (check-true (reports? problems #rx"is not readable")))

   (test-case "import descriptor naming another DLL is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define imp-rva (le-at bs (opt-pos bs 104) 4))
                           (define name-rva (le-at bs (+ (file-offset bs imp-rva) 12) 4))
                           (bytes-set! bs (file-offset bs name-rva) (char->integer #\x)))))
     (check-true (reports? problems #rx"mscoree.dll")))

   (test-case "first import that is not _CorExeMain is reported"
     (define problems
       (lint-damaged exe (λ (bs)
                           (define imp-rva (le-at bs (opt-pos bs 104) 4))
                           (define ft-rva (le-at bs (+ (file-offset bs imp-rva) 16) 4))
                           (define hint-rva (le-at bs (file-offset bs ft-rva) 4))
                           (bytes-set! bs (+ (file-offset bs hint-rva) 2) (char->integer #\x)))))
     (check-true (reports? problems #rx"_CorExeMain")))))

(test-case "input that is not a PE image is reported, not raised"
  (define garbage (make-temporary-file "rangi-lint-garbage-~a.bin"))
  (dynamic-wind
   void
   (λ ()
     (call-with-output-file garbage (λ (out) (write-bytes #"not a portable executable" out))
       #:exists 'truncate)
     (check-true (pair? (lint-image garbage))))
   (λ () (delete-file garbage))))
