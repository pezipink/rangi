#lang racket/base
; Win32 resource directory (PE/COFF, "The .rsrc Section"): the tree encoding, the RVAs of the
; payloads, the .win32resource syntax, and lowering. The walker below decodes the bytes from the
; spec's layout, so it does not reuse the encoder's own helpers.
(require rackunit
         racket/list
         "../src/pe/rsrc.rkt"
         "../src/pe/layout.rkt"
         "../src/pe/constants.rkt"
         "../src/ilasm/syntax.rkt"
         "../src/cli/lower.rkt")

(define test-params
  (image-params 'pe32+ machine-amd64 pe32plus-characteristics subsystem-windows-cui
                default-dll-characteristics default-image-base-pe32+
                default-section-align default-file-align))

(define (le32 n) (integer->integer-bytes n 4 #f #f))
(define (u16 b o) (integer-bytes->integer b #f #f o (+ o 2)))
(define (u32 b o) (integer-bytes->integer b #f #f o (+ o 4)))

; lays out the entries as a lone .rsrc section and renders it. Returns the placed image, the
; section bytes (index 0 is the section start), and the section's RVA.
(define (render-rsrc entries)
  (define chunks (win32-resource-chunks entries))
  (define img (layout-image test-params (list (section ".rsrc" section-chars-rsrc chunks))))
  (define ps (first (placed-image-sections img)))
  (define base (placed-section-rva ps))
  (define buf (make-bytes (placed-section-vsize ps) 0))
  (for ([p (in-list (placed-section-placements ps))])
    (bytes-copy! buf (- (placement-rva p) base) (render-chunk img p)))
  (values img buf base))

; Walks a directory at section offset off and returns (list path rva size) for each data entry.
; path is the list of IDs from the type level down. Named entries are not expected.
(define (leaves b off path)
  (check-equal? (u32 b off) 0 "Characteristics is zero")
  (check-equal? (u32 b (+ off 4)) 0 "TimeDateStamp is zero")
  (check-equal? (u16 b (+ off 12)) 0 "NumberOfNamedEntries is zero")
  (append*
   (for/list ([i (in-range (u16 b (+ off 14)))])
     (define e (+ off 16 (* 8 i)))
     (define here (append path (list (u32 b e))))
     (define target (u32 b (+ e 4)))
     (cond
       [(bitwise-bit-set? target 31)
        (leaves b (bitwise-and target #x7FFFFFFF) here)]
       [else
        (check-equal? (u32 b (+ target 8)) 0 "code page is zero")
        (check-equal? (u32 b (+ target 12)) 0 "reserved is zero")
        (list (list here (u32 b target) (u32 b (+ target 4))))]))))

(define sample
  (list (win32-entry 16 1 1036 #"de")
        (win32-entry 3 2 1033 #"xyz")
        (win32-entry 16 1 1033 #"abc")
        (win32-entry 16 2 1033 #"f")))

(test-case "a single entry encodes as a 24 + 24 + 24 byte directory chain and a 16 byte data entry"
  (define-values (img buf base) (render-rsrc (list (win32-entry 16 1 1033 #"abc"))))
  (check-equal? (chunk-size (placement-chunk (lookup-placement img rsrc-tree-chunk-name))) 88)
  ; root directory at offset 0: header, then one ID entry for type 16 whose subdirectory is at 24
  (check-equal? (subbytes buf 0 24)
                (bytes-append (make-bytes 14 0) (bytes 1 0)
                              (le32 16) (le32 (bitwise-ior #x80000000 24)))))

(test-case "the tree is the first chunk of the section, at section offset 0"
  (define chunks (win32-resource-chunks sample))
  (check-equal? (chunk-name (first chunks)) rsrc-tree-chunk-name)
  (define-values (img buf base) (render-rsrc sample))
  (check-equal? (placement-rva (lookup-placement img rsrc-tree-chunk-name)) base))

(test-case "entries sort by type, name, then language, with IDs ascending at each level"
  (define-values (img buf base) (render-rsrc sample))
  (check-equal? (map first (leaves buf 0 '()))
                '((3 2 1033) (16 1 1033) (16 1 1036) (16 2 1033))))

(test-case "each data entry's RVA resolves to its payload and its size is the payload length"
  (define-values (img buf base) (render-rsrc sample))
  (define found
    (for/list ([l (in-list (leaves buf 0 '()))])
      (define rva (second l))
      (define size (third l))
      (list (first l) (subbytes buf (- rva base) (+ (- rva base) size)))))
  (check-equal? found
                (list (list '(3 2 1033) #"xyz")
                      (list '(16 1 1033) #"abc")
                      (list '(16 1 1036) #"de")
                      (list '(16 2 1033) #"f"))))

(test-case "the same entries always encode to the same bytes"
  (define (encode es) (map chunk-bytes (win32-resource-chunks es)))
  (check-equal? (encode sample) (encode (reverse sample))))

(test-case "a duplicate (type, name, language) is rejected"
  (check-exn #rx"duplicate Win32 resource"
             (λ () (win32-resource-chunks (list (win32-entry 16 1 1033 #"a")
                                               (win32-entry 16 1 1033 #"b"))))))

(test-case "IDs outside 0..65535 are rejected"
  (check-exn #rx"not a 16-bit integer"
             (λ () (win32-resource-chunks (list (win32-entry 70000 1 1033 #"a")))))
  (check-exn #rx"not a 16-bit integer"
             (λ () (win32-resource-chunks (list (win32-entry 16 -1 1033 #"a"))))))

; a minimal module with a main method, plus the given top-level forms
(define (il-with . forms)
  (parse-il
   `((.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) (ret) })])
     ,@forms)))

(test-case ".win32resource parses to a decl with integer IDs and bytes"
  (define rs (module-model-win32-resources
              (il-with '(.win32resource 16 1 1033 (bytearray (01 02 03))))))
  (check-equal? (length rs) 1)
  (check-equal? (win32-resource-decl-type (first rs)) 16)
  (check-equal? (win32-resource-decl-name (first rs)) 1)
  (check-equal? (win32-resource-decl-lang (first rs)) 1033)
  (check-equal? (win32-resource-decl-bytes (first rs)) (bytes 1 2 3)))

(test-case "a module with no .win32resource has none"
  (check-equal? (module-model-win32-resources (il-with)) '()))

(test-case "a malformed or duplicate .win32resource is rejected"
  (check-exn #rx"outside 0..65535"
             (λ () (il-with '(.win32resource 65536 1 1033 (bytearray (01))))))
  (check-exn exn:fail?
             (λ () (il-with '(.win32resource 16 1 1033 (int32 1)))))
  (check-exn #rx"duplicate .win32resource"
             (λ () (il-with '(.win32resource 16 1 1033 (bytearray (01)))
                            '(.win32resource 16 1 1033 (bytearray (02)))))))

(test-case "lowering passes the win32 resources through to the cli program"
  (define cp (lower-module (il-with '(.win32resource 16 1 1033 (bytearray (01 02))))))
  (check-equal? (length (cli-program-win32-resources cp)) 1))
