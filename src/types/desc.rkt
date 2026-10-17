#lang racket/base
; Descriptors (layer 2 of docs/plans/types.md): what a type's members look like, in canonical
; references. Base, interfaces, methods and fields are promises, so building a descriptor reads
; only its header. Forcing a promise is what decodes signatures.
(require racket/promise
         "canon.rkt")
(provide (struct-out type-desc)
         (struct-out method-desc)
         (struct-out field-desc)
         subst-type
         subst-method
         instantiate-desc
         method->string)

; ref: the type's reference (with args for a closed instance).
; shape: 'class, 'interface, 'valuetype, 'enum or 'delegate. The finer kind; the reference's kind
;        is the IL element kind.
; base: promise of a reference or #f (interfaces have none).
; interfaces: promise of a list of references.
; methods, fields: promises of lists, in metadata row order.
(struct type-desc (ref shape abstract? sealed? base interfaces methods fields) #:transparent)

; owner: the reference that declares it (the instance, for a member of a closed generic).
; public?: the access is Public (II.23.1.10 and II.23.1.5); other members are kept, not dropped.
; params: canonical types, without a trailing '... (see vararg?).
; ret: a canonical type, or 'void.
(struct method-desc (owner name public? static? virtual? abstract? vararg? arity params ret)
  #:transparent)

(struct field-desc (owner name public? static? type) #:transparent)

; Replaces each (type-param 'type n) with (list-ref args n). Method-level parameters are left
; alone: generic method instantiation is not supported yet.
(define (subst-type t args)
  (cond
    [(symbol? t) t]
    [(type-param? t)
     (cond
       [(not (eq? (type-param-owner t) 'type)) t]
       [(< (type-param-index t) (length args)) (list-ref args (type-param-index t))]
       [else (error 'subst-type "type parameter !~a has no argument (have ~a)"
                    (type-param-index t) (length args))])]
    [(null? (type-ref-args t)) t]
    [else (with-args t (for/list ([a (in-list (type-ref-args t))]) (subst-type a args)))]))

(define (subst-method m owner args)
  (struct-copy method-desc m
               [owner owner]
               [params (for/list ([p (in-list (method-desc-params m))]) (subst-type p args))]
               [ret (subst-type (method-desc-ret m) args)]))

; The closed instance of an open generic descriptor. Its members are built on first force from
; the open ones, so the open descriptor is not changed.
(define (instantiate-desc open args)
  (define ref (with-args (type-desc-ref open) args))
  (type-desc
   ref
   (type-desc-shape open)
   (type-desc-abstract? open)
   (type-desc-sealed? open)
   (delay (let ([b (force (type-desc-base open))])
            (and b (subst-type b args))))
   (delay (for/list ([i (in-list (force (type-desc-interfaces open)))])
            (subst-type i args)))
   (delay (for/list ([m (in-list (force (type-desc-methods open)))])
            (subst-method m ref args)))
   (delay (for/list ([f (in-list (force (type-desc-fields open)))])
            (struct-copy field-desc f
                         [owner ref]
                         [type (subst-type (field-desc-type f) args)])))))

(define (method->string m)
  (define params (for/list ([p (in-list (method-desc-params m))]) (type->string p)))
  (format "~a~a ~a~a(~a~a)"
          (if (method-desc-static? m) "static " "")
          (type->string (method-desc-ret m))
          (method-desc-name m)
          (if (positive? (method-desc-arity m)) (format "`~a" (method-desc-arity m)) "")
          (join-strings params ", ")
          (if (method-desc-vararg? m) (if (null? params) "..." ", ...") "")))
