#lang racket/base
; The reference provider (layer 2 of docs/plans/types.md): descriptors read lazily from one
; assembly through the Rangi reader. This is the only types file that requires src/cli/.
;
; Building a descriptor reads its header row and nothing else. Its members, base and interfaces
; are promises, and forcing one decodes the signatures it needs (II.23.2).
(require racket/promise
         (only-in "../cli/reader.rkt" read-file read-assembly-meta row-column row-column-raw)
         (only-in "../cli/index.rkt" find-typedef find-exported-type typedef-methods typedef-fields
                  enclosing-type interface-impls)
         (only-in "../cli/sigs.rkt" decode-typespec decode-method-sig decode-field-sig
                  method-signature-ret method-signature-params method-signature-generic-arity
                  field-signature-type)
         "canon.rkt"
         "desc.rkt"
         "provider.rkt")
(provide open-reference-provider
         reference-decode-count
         reset-reference-decode-count!)

; rdr: the reader for the file. asm: the assembly identity. memo: (list ns name arity) -> TypeDef
; rid, for every type this provider has named. A nested type is found only through the memo,
; because its name carries its enclosing type's name, which is not in the reference alone.
(struct ctx (rdr asm memo))

; Signature decodes so far, for the laziness test: a member row is decoded only when forced.
(define decode-count 0)
(define (reference-decode-count) decode-count)
(define (reset-reference-decode-count!) (set! decode-count 0))

; "List`1" -> "List", 1 (II.10.7 generic arity suffix)
(define (split-arity name)
  (define m (regexp-match #rx"^(.*)`([0-9]+)$" name))
  (if m (values (cadr m) (string->number (caddr m))) (values name 0)))

(define (suffixed name arity)
  (if (positive? arity) (format "~a`~a" name arity) name))

(define (canonical-asm asm ns name)
  (if (and (member asm core-facades) (primitive-name? ns name)) core-asm asm))

(define (rid-for c ns name arity)
  (or (hash-ref (ctx-memo c) (list ns name arity) #f)
      (find-typedef (ctx-rdr c) ns (suffixed name arity))))

; The canonical name of a TypeDef. A nested type is "Outer/Inner" in its outermost namespace, and
; its arity is its own (a known limitation: see docs/plans/types.md).
(define (typedef-names c rid)
  (define rdr (ctx-rdr c))
  (define-values (base arity) (split-arity (row-column rdr 'typedef rid 'name)))
  (define enc (enclosing-type rdr rid))
  (cond
    [enc
     (define-values (ns outer _arity) (typedef-names c enc))
     (values ns (string-append outer "/" base) arity)]
    [else (values (row-column rdr 'typedef rid 'namespace) base arity)]))

; The namespace and name of an extends target, or #f #f when it is null or a TypeSpec.
(define (extends-name c ext)
  (define rdr (ctx-rdr c))
  (cond
    [(not ext) (values #f #f)]
    [(eq? (car ext) 'typedef)
     (values (row-column rdr 'typedef (cdr ext) 'namespace) (row-column rdr 'typedef (cdr ext) 'name))]
    [(eq? (car ext) 'typeref)
     (values (row-column rdr 'typeref (cdr ext) 'namespace) (row-column rdr 'typeref (cdr ext) 'name))]
    [else (values #f #f)]))

; 'interface, 'enum, 'valuetype, 'delegate or 'class, from the flags and the parent (II.23.1.15).
; System.Enum and System.ValueType are reference types even though they derive from ValueType.
(define (typedef-shape c rid ns name)
  (define rdr (ctx-rdr c))
  (define flags (row-column-raw rdr 'typedef rid 'flags))
  (define-values (pns pname) (extends-name c (row-column rdr 'typedef rid 'extends)))
  (define (parent? n) (and (equal? pns "System") (equal? pname n)))
  (cond
    [(positive? (bitwise-and flags #x20)) 'interface]
    [(member (list ns name) '(("System" "Enum") ("System" "ValueType"))) 'class]
    [(parent? "Enum") 'enum]
    [(parent? "ValueType") 'valuetype]
    [(parent? "MulticastDelegate") 'delegate]
    [else 'class]))

; The reference of a TypeDef, with its shape. The kind is the IL element kind, which is what a
; signature encodes: valuetype for structs and enums, class otherwise.
(define (typedef-info c rid)
  (define-values (ns name arity) (typedef-names c rid))
  (define shape (typedef-shape c rid ns name))
  (define kind (if (memq shape '(valuetype enum)) 'valuetype 'class))
  (hash-set! (ctx-memo c) (list ns name arity) rid)
  (values (type-ref (canonical-asm (ctx-asm c) ns name) ns name arity kind '()) shape))

; A TypeRef. Its kind comes from the signature that names it, since the target is not in this file.
(define (typeref-ref c rid kind)
  (define rdr (ctx-rdr c))
  (define-values (base arity) (split-arity (row-column rdr 'typeref rid 'name)))
  (define ns (row-column rdr 'typeref rid 'namespace))
  (define scope (row-column rdr 'typeref rid 'resolution-scope))
  (cond
    [(not scope) (error 'reference "TypeRef ~a has no resolution scope" base)]
    [(eq? (car scope) 'typeref)
     (define enc (typeref-ref c (cdr scope) 'class))
     (type-ref (type-ref-asm enc) (type-ref-namespace enc)
               (string-append (type-ref-name enc) "/" base) arity kind '())]
    [(eq? (car scope) 'assemblyref)
     (define asm (row-column rdr 'assemblyref (cdr scope) 'name))
     (type-ref (canonical-asm asm ns base) ns base arity kind '())]
    [else (type-ref (ctx-asm c) ns base arity kind '())]))

; A TypeDefOrRef coded token, or a TypeSpec, as a reference of the given kind.
(define (tok->type c tok kind)
  (define rdr (ctx-rdr c))
  (cond
    [(eq? (car tok) 'typedef)
     (let-values ([(r _shape) (typedef-info c (cdr tok))]) r)]
    [(eq? (car tok) 'typeref) (typeref-ref c (cdr tok) kind)]
    [(eq? (car tok) 'typespec)
     (sig->type c (decode-typespec (row-column rdr 'typespec (cdr tok) 'signature)))]
    [else (error 'reference "unexpected type token ~a" (car tok))]))

; A decoded Type (II.23.2.12) as a canonical type. Custom modifiers are dropped.
(define (sig->type c t)
  (cond
    [(eq? t 'void) 'void]
    [(symbol? t) (primitive-ref t)]
    [(eq? (car t) 'class) (tok->type c (cadr t) 'class)]
    [(eq? (car t) 'valuetype) (tok->type c (cadr t) 'valuetype)]
    [(eq? (car t) 'genericinst)
     (with-args (sig->type c (cadr t))
                (for/list ([a (in-list (caddr t))]) (sig->type c a)))]
    [(eq? (car t) 'var) (type-param 'type (cadr t))]
    [(eq? (car t) 'mvar) (type-param 'method (cadr t))]
    [(eq? (car t) 'szarray) (type-ref #f "" "" 0 'szarray (list (sig->type c (cadr t))))]
    [(eq? (car t) 'byref) (type-ref #f "" "" 0 'byref (list (sig->type c (cadr t))))]
    [(eq? (car t) 'ptr) (type-ref #f "" "" 0 'ptr (list (sig->type c (cadr t))))]
    ; Bounds and sizes are dropped: an array is its element type and rank (a known limitation).
    [(eq? (car t) 'array) (type-ref #f "" "" (caddr t) 'array (list (sig->type c (cadr t))))]
    [(memq (car t) '(modreq modopt)) (sig->type c (caddr t))]
    [(eq? (car t) 'fnptr) (error 'reference "function pointer types are not supported yet")]
    [else (error 'reference "unexpected signature element ~a" (car t))]))

(define (method-desc-of c owner m)
  (define rdr (ctx-rdr c))
  (set! decode-count (add1 decode-count))
  (define flags (row-column-raw rdr 'methoddef m 'flags))
  (define sig (decode-method-sig (row-column rdr 'methoddef m 'signature)))
  (define ps (method-signature-params sig))
  (method-desc owner
               (row-column rdr 'methoddef m 'name)
               ; II.23.1.10 MethodAttributes: access mask 0x7, Public is 6
               (= (bitwise-and flags 7) 6)
               (positive? (bitwise-and flags #x10))
               (positive? (bitwise-and flags #x40))
               (positive? (bitwise-and flags #x400))
               (and (memq '... ps) #t)
               (method-signature-generic-arity sig)
               (for/list ([p (in-list ps)] #:unless (eq? p '...)) (sig->type c p))
               (sig->type c (method-signature-ret sig))))

(define (field-desc-of c owner f)
  (define rdr (ctx-rdr c))
  (set! decode-count (add1 decode-count))
  (define flags (row-column-raw rdr 'field f 'flags))
  (define sig (decode-field-sig (row-column rdr 'field f 'signature)))
  ; II.23.1.5 FieldAttributes: access mask 0x7, Public is 6
  (field-desc owner
              (row-column rdr 'field f 'name)
              (= (bitwise-and flags 7) 6)
              (positive? (bitwise-and flags #x10))
              (sig->type c (field-signature-type sig))))

(define (typedef-desc c rid)
  (define rdr (ctx-rdr c))
  (define-values (r shape) (typedef-info c rid))
  (define flags (row-column-raw rdr 'typedef rid 'flags))
  (define ext (row-column rdr 'typedef rid 'extends))
  (type-desc r shape
             (positive? (bitwise-and flags #x80))
             (positive? (bitwise-and flags #x100))
             (delay (and ext (tok->type c ext 'class)))
             (delay (for/list ([i (in-list (interface-impls rdr rid))])
                      (tok->type c (row-column rdr 'interfaceimpl i 'interface) 'class)))
             (delay (let-values ([(start end) (typedef-methods rdr rid)])
                      (for/list ([m (in-range start end)]) (method-desc-of c r m))))
             (delay (let-values ([(start end) (typedef-fields rdr rid)])
                      (for/list ([f (in-range start end)]) (field-desc-of c r f))))))

; The assembly name of a file without metadata, e.g. "C:/x/Foo.dll" -> "Foo".
(define (module-name path)
  (define-values (base name dir?) (split-path path))
  (path->string (path-replace-extension name #"")))

; II.23.1.15 TypeAttributes: the visibility mask (low 3 bits) is Public = 1 for a top-level type and
; NestedPublic = 2 for a nested one. Namespace lookup answers only public types; signatures may
; still name non-public types, so by-ref does not check.
(define (public-typedef? c rid)
  (memv (bitwise-and (row-column-raw (ctx-rdr c) 'typedef rid 'flags) 7) '(1 2)))

(define (open-reference-provider path)
  (define rdr (read-file path))
  (define asm (or (read-assembly-meta rdr) (module-name path)))
  (define c (ctx rdr asm (make-hash)))
  (provider asm
            (λ (ns name arity)
              (define rid (rid-for c ns name arity))
              (and rid (public-typedef? c rid) (typedef-desc c rid)))
            (λ (r)
              (define rid (rid-for c (type-ref-namespace r) (type-ref-name r) (type-ref-arity r)))
              (and rid (typedef-desc c rid)))
            #t
            #f))
