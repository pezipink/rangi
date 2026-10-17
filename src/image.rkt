#lang racket/base
(require racket/match
         racket/file
         racket/path
         (only-in "ilasm/syntax.rkt" module-model-dll?)
         "cli/lower.rkt"
         "cli/build.rkt"
         "cli/header.rkt"
         "pe/constants.rkt"
         "pe/imports.rkt"
         "pe/layout.rkt"
         "pe/relocs.rkt"
         "pe/write.rkt")
(provide write-image assemble image-layout-report)

; ---------------------------------------------------------------------------
; layout constants (the PE layout itself lives in pe/)

(define image-bases (hasheq 'pe32 default-image-base-pe32 'pe32+ default-image-base-pe32+))
(define section-align default-section-align)
(define file-align default-file-align)

; data directory index -> name of the chunk it covers
(define pe-data-dirs (list (cons dir-import-table 'import-dir)
                           (cons dir-base-relocation-table 'reloc)
                           (cons dir-iat 'iat)
                           (cons dir-clr-runtime-header 'cli-header)))

; writes the module model to out-path and returns out-path
(define (write-image m out-path)
  (write-pe-image (plan-image (lower-module m) (path->string (file-name-from-path out-path))
                              #:dll? (module-model-dll? m))
                  out-path
                  #:entry 'entry-stub
                  #:dirs pe-data-dirs)
  out-path)

(define (assemble m [out-path (make-temporary-file "rangi-~a.exe")])
  (write-image m out-path))

; layout of the image that assemble writes for a file called file-name (V5 snapshots)
(define (image-layout-report m [file-name "image.exe"])
  (layout-report (plan-image (lower-module m) file-name #:dll? (module-model-dll? m))))

(define (pe-subsystem name)
  (case name
    [(console) subsystem-windows-cui]
    [(windows) subsystem-windows-gui]
    [else (error 'pe-subsystem "unknown subsystem ~a" name)]))

; places every chunk and returns the placed image, without writing a file
(define (plan-image p file-name #:dll? [dll? #f])
  (define asm-name (regexp-replace #rx"[.][^.]*$" file-name ""))
  (define mod-name (or (cli-program-module-name p) file-name))
  (define entry-rid (cli-program-entry-rid p))
  (define fmt (cli-program-format p))
  (define all-mdefs
    (for*/list ([td (in-list (cli-program-typedefs p))] [m (in-list (tdef-methods td))]) m))

  (define md (build-metadata p asm-name mod-name))
  (match-define (list iat import-dir lookup hint-name dll-name entry-stub)
    (mscoree-chunks fmt #:dll? dll?))
  (define cli-header
    (cli-header-chunk #:metadata-size (bytes-length (chunk-bytes md))
                      #:entry-rid entry-rid
                      #:flags (cli-platform-flags (cli-program-platform p))))
  (define body-chunks
    (for/list ([m (in-list all-mdefs)] [i (in-naturals)] #:when (mdef-body m))
      (chunk (method-sym i) dword-align (mdef-body m) '())))
  (define text
    (section ".text" section-chars-text
             (append (list iat cli-header md) body-chunks
                     (list import-dir lookup hint-name dll-name entry-stub))))

  (define chars-base (if (eq? fmt 'pe32+) pe32plus-characteristics pe32-characteristics))
  (define chars (if dll? (bitwise-ior chars-base image-file-dll) chars-base))
  (define subsystem (pe-subsystem (cli-program-subsystem p)))
  (define params
    (if (eq? fmt 'pe32+)
        (image-params 'pe32+ machine-amd64 chars subsystem
                      default-dll-characteristics (hash-ref image-bases fmt) section-align file-align)
        (image-params 'pe32 machine-i386 chars subsystem
                      default-dll-characteristics (hash-ref image-bases fmt) section-align file-align)))
  ; the relocation table holds the addresses of .text, so lay out .text before building it
  (define reloc
    (section ".reloc" section-chars-reloc
             (list (base-relocation-chunk (layout-image params (list text))))))
  (layout-image params (list text reloc)))
