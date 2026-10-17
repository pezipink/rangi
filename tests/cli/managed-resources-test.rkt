#lang racket/base
; Embedded managed resources (II.22.24, II.25.3.3). A .mresource directive lowers to a
; ManifestResource row whose Offset points at its length prefix in the CLI resources blob, and the
; CLI header's Resources directory points at the blob.
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/header.rkt"
         "../../src/cli/tables.rkt"
         "../../src/pe/model.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

; A <Module> entry point and the given top-level forms.
(define (il-with . forms)
  (parse-il
   `((.assembly extern ,mscorlib-path {})
     (.assembly donothing {})
     (.module local.exe)
     (.class (private auto ansi) <Module>
       [(.method (public static) void main () (cil managed)
          { (.entrypoint) (.maxstack 8) (ret) })])
     ,@forms)))

(define two-resources
  '((.mresource public Data (bytearray (01 02 03)))
    (.mresource private Other (bytearray (AA BB)))))

; the lowered ManifestResource list of a parsed module
(define (lower-resources-of m)
  (cli-program-resources (lower-module m)))

(test-case "a .mresource parses to a resource-decl with its flags, name, and bytes"
  (define rs (module-model-resources (il-with '(.mresource public Data (bytearray (01 02 03))))))
  (check-equal? (length rs) 1)
  (check-equal? (resource-decl-name (first rs)) 'Data)
  (check-equal? (resource-decl-flags (first rs)) 'public)
  (check-equal? (resource-decl-bytes (first rs)) (bytes 1 2 3)))

(test-case "a module with no .mresource has no resources"
  (check-equal? (module-model-resources (il-with)) '()))

(test-case "a .mresource needs public or private and a bytearray"
  (check-exn exn:fail? (λ () (il-with '(.mresource Data (bytearray (01))))))
  (check-exn exn:fail? (λ () (il-with '(.mresource internal Data (bytearray (01))))))
  (check-exn exn:fail? (λ () (il-with '(.mresource public Data (int32 1))))))

(test-case "a duplicate .mresource name is rejected"
  (check-exn #rx"duplicate .mresource Data"
             (λ () (il-with '(.mresource public Data (bytearray (01)))
                            '(.mresource private Data (bytearray (02)))))))

(test-case "offsets are the running total of length prefixes and data, with flags public = 1"
  (define rs (lower-resources-of (apply il-with two-resources)))
  (check-equal? (map manifest-resource-name rs) '("Data" "Other"))
  ; first at 0 (4 + 3 bytes), second at 7 (after 4 + 3)
  (check-equal? (map manifest-resource-offset rs) '(0 7))
  ; ManifestResource flags: public = 1, private = 2
  (check-equal? (map manifest-resource-flags rs) '(1 2))
  (check-equal? (map manifest-resource-data rs) (list (bytes 1 2 3) (bytes #xAA #xBB))))

(test-case "the CLI resources blob is a u32 little-endian length then the bytes for each resource"
  (define rs (lower-resources-of (apply il-with two-resources)))
  (check-equal? (resources-blob rs)
                (bytes 3 0 0 0 1 2 3 2 0 0 0 #xAA #xBB)))

(test-case "no resources gives an empty blob"
  (check-equal? (resources-blob '()) #""))

(test-case "each ManifestResource row holds the offset, flags, name, and implementation null (in-file)"
  (define cp (lower-module (apply il-with two-resources)))
  (define captured #f)
  (build-metadata cp "rangi-test" "rangi.dll"
                  #:extra (λ (tb sh bh) (set! captured tb)))
  (define rows (table-rows captured 'manifestresource))
  (check-equal? (map (λ (r) (list (first r) (second r) (fourth r))) rows)
                '((0 1 0) (7 2 0))))

(test-case "the CLI header points its Resources directory at the blob and records its size"
  (define hdr
    (cli-header-chunk #:metadata-size 0 #:entry-rid #f #:resources-size 13))
  ; Resources RVA is at offset 24, its size at offset 28 (II.25.3.3)
  (check-equal? (subbytes (chunk-bytes hdr) 28 32) (bytes 13 0 0 0))
  (check-equal? (subbytes (chunk-bytes hdr) 24 28) (bytes 0 0 0 0))
  (check-not-false
   (findf (λ (f) (and (eq? (fixup-kind f) 'rva32)
                      (= (fixup-offset f) 24)
                      (eq? (fixup-target f) 'cli-resources)))
          (chunk-fixups hdr))))

(test-case "the CLI header without resources has a zero Resources directory and no fixup"
  (define hdr (cli-header-chunk #:metadata-size 0 #:entry-rid #f))
  (check-equal? (subbytes (chunk-bytes hdr) 24 32) (make-bytes 8 0))
  (check-false
   (findf (λ (f) (= (fixup-offset f) 24)) (chunk-fixups hdr))))
