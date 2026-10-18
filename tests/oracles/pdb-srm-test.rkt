#lang racket/base
; A two-document program's portable PDB and debug directory against System.Reflection.Metadata
; (tests/oracles/pdb-dump). SRM must decode the sequence points that lowering produced, name both
; documents, and associate the sidecar with the image. With debug off there is no sidecar and no
; debug directory. Output is byte-identical across runs.
(require rackunit racket/file racket/list racket/string
         "../lib/srm.rkt" "../../src/ilasm/syntax.rkt" "../../src/cli/lower.rkt"
         "../../src/image.rkt" "tools.rkt")

(define mscorlib-ref
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program-forms)
  `((.assembly extern ,mscorlib-ref {})
    (.assembly prog {})
    (.module prog.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed)
         { (.entrypoint)
           (.line 3 4 3 10 "a.il")
           (ldc.i4.1)
           (pop)
           (.line 4 4 4 12 "b.il")
           (ret) })])))

(define (main-mdef)
  (define prog (lower-module (parse-il (program-forms))))
  (findf (λ (m) (equal? (mdef-name m) "main"))
         (append-map tdef-methods (cli-program-typedefs prog))))

; the lines of pdb-dump output that start with prefix
(define (lines-with prefix out)
  (filter (λ (l) (string-prefix? l prefix)) (string-split out "\n")))

; "doc N name" lines to a hash from document name to its 1-based row
(define (doc-rows out)
  (for/hash ([l (in-list (lines-with "doc " out))])
    (define m (regexp-match #px"^doc ([0-9]+) (.*)$" l))
    (values (caddr m) (string->number (cadr m)))))

(define (with-temp-dir proc)
  (define dir (make-temporary-file "rangi-pdb-~a" 'directory))
  (dynamic-wind void
                (λ () (proc dir))
                (λ () (delete-directory/files dir #:must-exist? #f))))

(define (read-bytes-of path)
  (call-with-input-file path (λ (in) (read-bytes (file-size path) in))))

(cond
  [srm-dotnet
   (build-pdb-dump! srm-dotnet)
   (with-temp-dir
    (λ (dir)
      (define exe (build-path dir "prog.exe"))
      (define pdb (build-path dir "prog.pdb"))
      (assemble (parse-il (program-forms)) exe)

      (define-values (pdb-code pdb-out pdb-err) (run-pdb-dump srm-dotnet pdb))
      (define-values (img-code img-out img-err) (run-pdb-dump srm-dotnet exe))

      (test-case "pdb-dump reads the sidecar and the image"
        (check-equal? pdb-code 0 pdb-err)
        (check-equal? img-code 0 img-err))

      (test-case "SRM reads the PDB header and the entry point"
        (check-equal? (lines-with "version " pdb-out) '("version PDB v1.0"))
        (check-equal? (lines-with "entry " pdb-out) '("entry 0x06000001")))

      (test-case "SRM names both documents in row order"
        (check-equal? (doc-rows pdb-out) (hash "a.il" 1 "b.il" 2)))

      (test-case "SRM decodes the sequence points Rangi lowered"
        (define rows (doc-rows pdb-out))
        (define expected
          (for/list ([sp (in-list (methoddebug-seqpts (mdef-debug (main-mdef))))])
            (format "sp ~a ~a ~a ~a ~a ~a"
                    (seqpt-offset sp) (seqpt-start-line sp) (seqpt-start-col sp)
                    (seqpt-end-line sp) (seqpt-end-col sp)
                    (hash-ref rows (seqpt-file sp)))))
        (check-equal? (lines-with "sp " pdb-out) expected)
        (check-equal? (length expected) 2))

      (test-case "a method whose sequence points span two documents has a nil document"
        (check-equal? (lines-with "method " pdb-out) '("method 1 doc nil localsig 0")))

      (test-case "the image has a CodeView, a PdbChecksum and a Reproducible entry"
        (define types (map (λ (l) (cadr (regexp-match #px"^debug type ([0-9]+) " l)))
                           (lines-with "debug type " img-out)))
        (check-equal? types '("2" "19" "16"))
        (check-equal? (lines-with "codeview " img-out)
                      (list (format "codeview guid ~a age 1 path prog.pdb"
                                    (cadr (regexp-match #px"codeview guid ([0-9a-f]{32})" img-out)))))
        (check-true (regexp-match? #px"(?m:^checksum SHA256 [0-9a-f]{64}$)" img-out)))

      (test-case "SRM associates the sidecar with the image"
        (check-equal? (lines-with "associated " img-out)
                      '("associated true" "associated path prog.pdb")))

      (test-case "the same program assembles to identical image and PDB bytes"
        (define dir2 (build-path dir "again"))
        (make-directory dir2)
        (define exe2 (build-path dir2 "prog.exe"))
        (assemble (parse-il (program-forms)) exe2)
        (check-equal? (read-bytes-of exe2) (read-bytes-of exe))
        (check-equal? (read-bytes-of (build-path dir2 "prog.pdb")) (read-bytes-of pdb)))

      (test-case "debug off writes no sidecar and no debug directory"
        (define off (build-path dir "off"))
        (make-directory off)
        (define off-exe (build-path off "prog.exe"))
        (assemble (parse-il (program-forms)) off-exe #:debug? #f)
        (check-false (file-exists? (build-path off "prog.pdb")))
        (define-values (code out err) (run-pdb-dump srm-dotnet off-exe))
        (check-equal? code 0 err)
        (check-equal? (lines-with "debug type " out) '())
        (check-equal? (lines-with "associated " out) '("associated false")))))]
  [else
   (oracle-missing "dotnet")])
