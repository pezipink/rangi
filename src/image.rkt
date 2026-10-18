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
         "pdb/pdb.rkt"
         "pe/constants.rkt"
         "pe/imports.rkt"
         "pe/layout.rkt"
         "pe/model.rkt"
         "pe/relocs.rkt"
         "pe/rsrc.rkt"
         "pe/write.rkt"
         (only-in "private/binary.rkt" le))
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

; writes the module model to out-path, with its portable PDB next to it (out-path with a .pdb
; extension) when debug is on, and returns out-path
(define (write-image m out-path #:debug? [debug? #t])
  (define p (lower-module m))
  (define-values (placed pdb)
    (plan-image p (path->string (file-name-from-path out-path))
                #:dll? (module-model-dll? m)
                #:debug? debug?))
  (write-pe-image placed
                  out-path
                  #:entry 'entry-stub
                  #:dirs (image-data-dirs p (and pdb #t)))
  (when pdb
    (call-with-output-file (path-replace-extension out-path #".pdb")
      (λ (out) (write-bytes (pdb-image-bytes pdb) out))
      #:exists 'truncate))
  out-path)

; the debug directory (data directory index 6) is listed only when there is a PDB, and the Win32
; resource directory (index 2) only when there are resources
(define (image-data-dirs p debug?)
  (define dirs (if debug? (cons (cons dir-debug 'debug-dir) pe-data-dirs) pe-data-dirs))
  (if (null? (cli-program-win32-resources p))
      dirs
      (cons (cons dir-resource-table rsrc-tree-chunk-name) dirs)))

(define (assemble m [out-path (make-temporary-file "rangi-~a.exe")] #:debug? [debug? #t])
  (write-image m out-path #:debug? debug?))

; layout of the image that assemble writes for a file called file-name (V5 snapshots)
(define (image-layout-report m [file-name "image.exe"])
  (define-values (placed pdb)
    (plan-image (lower-module m) file-name #:dll? (module-model-dll? m)))
  (layout-report placed))

(define (pe-subsystem name)
  (case name
    [(console) subsystem-windows-cui]
    [(windows) subsystem-windows-gui]
    [else (error 'pe-subsystem "unknown subsystem ~a" name)]))

; The debug directory (PE/COFF, The .debug Section) and the data its entries point at. Each entry is
; 28 bytes: Characteristics, TimeDateStamp, Major and MinorVersion, Type, SizeOfData,
; AddressOfRawData (an rva32 fixup) and PointerToRawData (a file-offset fixup).
(define debug-entry-size 28)
(define debug-type-codeview 2)
(define debug-type-pdb-checksum 19)
(define debug-type-reproducible 16)

; Returns the directory chunk and the chunks its entries point at. The CodeView RSDS record holds
; the PDB Id's GUID (its first 16 bytes), age 1 and the PDB file name. The Id's last four bytes
; are the entry's TimeDateStamp. The PdbChecksum record is the SHA-256 of the PDB file.
(define (debug-directory pdb pdb-name)
  (define id (pdb-image-id pdb))
  (define codeview-data
    (bytes-append #"RSDS" (subbytes id 0 16) (le 1 4) (string->bytes/utf-8 pdb-name) #"\0"))
  (define checksum-data (bytes-append #"SHA256\0" (pdb-image-checksum pdb)))
  (define codeview-chunk (chunk 'debug-codeview dword-align codeview-data '()))
  (define checksum-chunk (chunk 'debug-checksum dword-align checksum-data '()))
  ; type, MinorVersion, SizeOfData, TimeDateStamp bytes, and the data chunk name (or #f)
  (define entries
    (list (list debug-type-codeview #x504D (bytes-length codeview-data) (subbytes id 16 20) 'debug-codeview)
          (list debug-type-pdb-checksum 0 (bytes-length checksum-data) (le 0 4) 'debug-checksum)
          (list debug-type-reproducible 0 0 (le 0 4) #f)))
  (define (entry-bytes type minor size stamp)
    (bytes-append (le 0 4) stamp (le 0 2) (le minor 2) (le type 4) (le size 4) (le 0 4) (le 0 4)))
  (define dir-bytes
    (apply bytes-append
           (for/list ([e (in-list entries)])
             (entry-bytes (first e) (second e) (third e) (fourth e)))))
  (define fixups
    (append*
     (for/list ([e (in-list entries)] [i (in-naturals)] #:when (fifth e))
       (define at (+ (* i debug-entry-size) 20))
       (list (fixup at 'rva32 (fifth e))
             (fixup (+ at 4) 'file-offset (fifth e))))))
  (values (chunk 'debug-dir dword-align dir-bytes fixups)
          (list codeview-chunk checksum-chunk)))

; places every chunk and returns the placed image and the PDB (#f without debug), without writing
; files. The PDB depends only on the method debug data, so it does not depend on the layout.
(define (plan-image p file-name #:dll? [dll? #f] #:debug? [debug? #t])
  (define asm-name (regexp-replace #rx"[.][^.]*$" file-name ""))
  (define mod-name (or (cli-program-module-name p) file-name))
  (define entry-rid (cli-program-entry-rid p))
  (define fmt (cli-program-format p))
  (define all-mdefs
    (for*/list ([td (in-list (cli-program-typedefs p))] [m (in-list (tdef-methods td))]) m))
  (define pdb
    (and debug?
         (build-pdb (map mdef-debug all-mdefs)
                    #:entry-point (if entry-rid (bitwise-ior #x06000000 entry-rid) 0)
                    #:standalone-sig-count (length (cli-program-standalone-sigs p)))))
  (define-values (debug-dir debug-data)
    (if pdb
        (debug-directory pdb (string-append asm-name ".pdb"))
        (values #f '())))

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
                     (list import-dir lookup hint-name dll-name entry-stub)
                     (if debug-dir (cons debug-dir debug-data) '()))))
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
  (values (layout-image params (append (list text) sdata rsrc (list reloc)))
          pdb))
