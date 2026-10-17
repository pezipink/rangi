#lang racket/base
; Canonical type references (layer 1 of docs/plans/types.md). Pure data: no reader, no providers.
;
; Two spellings of one type give equal? references, so `int`, `int32` and the metadata name
; System.Int32 all reduce to the same struct. The structs are prefab, so a reference can be
; quoted into syntax (a declaration's binding does this), and equal? and equal-hash-code work.
(provide (struct-out type-ref)
         (struct-out type-param)
         core-asm
         primitive-ref
         primitive-name?
         core-facades
         source-primitive
         with-args
         with-asm
         type->string
         join-strings)

; asm: the assembly identity: "mscorlib", or the module's name for a local type. #f for the
;      constructed kinds, which no assembly owns.
; namespace, name: strings. name has no generic arity suffix ("List", not "List`1"). A nested
;      type is "Outer/Inner" in its outermost namespace.
; arity: generic parameter count. For 'array it is the rank.
; kind: 'class or 'valuetype, the IL element kind (what a signature encodes). The constructed
;      kinds are 'szarray, 'array, 'byref and 'ptr.
; args: type arguments of a generic instantiation. For a constructed kind, the one element type.
(struct type-ref (asm namespace name arity kind args) #:prefab)

; A generic parameter, by owner ('type or 'method) and index (II.23.2.12 VAR and MVAR).
(struct type-param (owner index) #:prefab)

; The assembly that defines the primitive types. Its identity is fixed here, so the spellings of
; a primitive agree whichever provider found it.
(define core-asm "mscorlib")

; element type -> namespace, name, IL kind (II.23.1.16)
(define primitive-table
  '((boolean "System" "Boolean" valuetype)
    (char "System" "Char" valuetype)
    (int8 "System" "SByte" valuetype)
    (uint8 "System" "Byte" valuetype)
    (int16 "System" "Int16" valuetype)
    (uint16 "System" "UInt16" valuetype)
    (int32 "System" "Int32" valuetype)
    (uint32 "System" "UInt32" valuetype)
    (int64 "System" "Int64" valuetype)
    (uint64 "System" "UInt64" valuetype)
    (float32 "System" "Single" valuetype)
    (float64 "System" "Double" valuetype)
    (intptr "System" "IntPtr" valuetype)
    (uintptr "System" "UIntPtr" valuetype)
    (typedref "System" "TypedReference" valuetype)
    (string "System" "String" class)
    (object "System" "Object" class)))

; The reference for a primitive element type, or #f for void (which is not a type).
(define (primitive-ref sym)
  (define e (assq sym primitive-table))
  (and e (type-ref core-asm (cadr e) (caddr e) 0 (cadddr e) '())))

(define (primitive-name? ns name)
  (for/or ([e (in-list primitive-table)])
    (and (equal? ns (cadr e)) (equal? name (caddr e)))))

; Assemblies that stand in for the core library in .NET Core and later. A primitive typed in any
; of them is the mscorlib primitive, so it is canonicalised to core-asm. Other core types keep
; their facade's name until forwarding is implemented.
(define core-facades '("mscorlib" "System.Runtime" "netstandard" "System.Private.CoreLib"))

; C# keywords that name a primitive. The IL spellings (int32, float64, ...) need no entry; they
; are the element symbols themselves.
(define keyword-symbols
  (make-immutable-hash
   '(("bool" . boolean) ("sbyte" . int8) ("byte" . uint8) ("short" . int16) ("ushort" . uint16)
     ("int" . int32) ("uint" . uint32) ("long" . int64) ("ulong" . uint64)
     ("float" . float32) ("double" . float64) ("nint" . intptr) ("nuint" . uintptr))))

; A source spelling of a primitive, as a reference, or #f. The metadata names (System.Int32) are
; found through the providers and reduce to the same reference, so they are not listed here.
(define (source-primitive text)
  (define sym
    (or (hash-ref keyword-symbols text #f)
        (let ([s (string->symbol text)]) (and (assq s primitive-table) s))))
  (and sym (primitive-ref sym)))

(define (with-args r args)
  (type-ref (type-ref-asm r) (type-ref-namespace r) (type-ref-name r) (type-ref-arity r)
            (type-ref-kind r) args))

(define (with-asm r asm)
  (type-ref asm (type-ref-namespace r) (type-ref-name r) (type-ref-arity r)
            (type-ref-kind r) (type-ref-args r)))

; A readable form for messages and demos: System.Collections.Generic.List<System.Int32>.
(define (type->string t)
  (cond
    [(symbol? t) (symbol->string t)]
    [(type-param? t)
     (format "~a~a" (if (eq? (type-param-owner t) 'method) "!!" "!") (type-param-index t))]
    [else
     (define args (type-ref-args t))
     (case (type-ref-kind t)
       [(szarray) (string-append (type->string (car args)) "[]")]
       [(array) (string-append (type->string (car args))
                               "[" (make-string (sub1 (type-ref-arity t)) #\,) "]")]
       [(byref) (string-append (type->string (car args)) "&")]
       [(ptr) (string-append (type->string (car args)) "*")]
       [else
        (define ns (type-ref-namespace t))
        (define base (if (equal? ns "")
                         (type-ref-name t)
                         (string-append ns "." (type-ref-name t))))
        (cond
          [(pair? args)
           (string-append base "<" (join-strings (map type->string args) ", ") ">")]
          [(positive? (type-ref-arity t)) (format "~a`~a" base (type-ref-arity t))]
          [else base])])]))

(define (join-strings strs sep)
  (cond
    [(null? strs) ""]
    [else (for/fold ([acc (car strs)]) ([s (in-list (cdr strs))]) (string-append acc sep s))]))
