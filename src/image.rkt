#lang racket/base
(require racket/match
         racket/file
         racket/list
         racket/path
         (only-in "ilasm/syntax.rkt"
                  module-model-dll?
                  win32-resource-decl-type win32-resource-decl-name
                  win32-resource-decl-lang win32-resource-decl-bytes)
         "cli/lower.rkt"
         "cli/build.rkt"
         "cli/header.rkt"
         "pe/constants.rkt"
         "pe/imports.rkt"
         "pe/layout.rkt"
         "pe/relocs.rkt"
         "pe/rsrc.rkt"
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
  (define p (lower-module m))
  (write-pe-image (plan-image p (path->string (file-name-from-path out-path))
                              #:dll? (module-model-dll? m))
                  out-path
                  #:entry 'entry-stub
                  #:dirs (image-data-dirs p))
  out-path)

; the Win32 resource directory (data directory index 2) is listed only when there are resources
(define (image-data-dirs p)
  (if (null? (cli-program-win32-resources p))
      pe-data-dirs
      (cons (cons dir-resource-table rsrc-tree-chunk-name) pe-data-dirs)))

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
  ; the CLI resources blob (II.25.3.3) is placed after the metadata, and only when there are
  ; resources, so images without them keep their layout
  (define res-bytes (resources-blob (cli-program-resources p)))
  (define cli-header
    (cli-header-chunk #:metadata-size (bytes-length (chunk-bytes md))
                      #:entry-rid entry-rid
                      #:resources-size (bytes-length res-bytes)
                      #:flags (cli-platform-flags (cli-program-platform p))))
  (define res-chunks
    (if (zero? (bytes-length res-bytes))
        '()
        (list (chunk 'cli-resources dword-align res-bytes '()))))
  (define body-chunks
    (for/list ([m (in-list all-mdefs)] [i (in-naturals)] #:when (mdef-body m))
      (chunk (method-sym i) dword-align (mdef-body m) '())))
  (define text
    (section ".text" section-chars-text
             (append (list iat cli-header md) res-chunks body-chunks
                     (list import-dir lookup hint-name dll-name entry-stub))))
  ; initial data of FieldRVA fields (II.22.18), in Field-row order; the section is added only when
  ; some field has data, so images without static data keep their layout
  (define data-chunks
    (for/list ([f (in-list (append-map tdef-fields (cli-program-typedefs p)))]
               [rid (in-naturals 1)]
               #:when (fdef-data f))
      (chunk (field-data-sym rid) dword-align (fdef-data f) '())))
  (define sdata
    (if (null? data-chunks)
        '()
        (list (section ".sdata" section-chars-sdata data-chunks))))
  ; the Win32 resource tree (PE/COFF, The .rsrc Section) is added only when there are resources
  (define win32-entries
    (for/list ([d (in-list (cli-program-win32-resources p))])
      (win32-entry (win32-resource-decl-type d) (win32-resource-decl-name d)
                   (win32-resource-decl-lang d) (win32-resource-decl-bytes d))))
  (define rsrc
    (if (null? win32-entries)
        '()
        (list (section ".rsrc" section-chars-rsrc (win32-resource-chunks win32-entries)))))

  (define chars-base
    (bitwise-ior (if (eq? fmt 'pe32+) pe32plus-characteristics pe32-characteristics)
                 (if (cli-platform-requires-32bit? (cli-program-platform p))
                     image-file-32bit-machine
                     0)))
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
  (layout-image params (append (list text) sdata rsrc (list reloc))))
