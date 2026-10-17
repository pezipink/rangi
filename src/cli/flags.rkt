#lang racket/base
; Field and parameter flag values (ECMA-335 II.23.1) as named constants, and the keyword
; lists that turn a source-level modifier list into the integer stored in the table row.
; The values match System.Reflection.Metadata's FieldAttributes and ParameterAttributes.
(provide fa-privatescope fa-private fa-famandassem fa-assembly fa-family fa-famorassem
         fa-public fa-access-mask fa-static fa-initonly fa-literal fa-notserialized
         fa-hasfieldrva fa-specialname fa-rtspecialname fa-hasfieldmarshal fa-pinvokeimpl
         fa-hasdefault fa-reserved-mask
         pa-in pa-out pa-lcid pa-retval pa-optional pa-hasdefault pa-hasfieldmarshal
         pa-reserved3 pa-reserved4 pa-reserved-mask
         field-attributes-flags
         param-attributes-flags
         pinvoke-attributes-flags
         generic-param-attributes-flags)

; II.23.1.5 FieldAttributes. The access field is a 3-bit value (FieldAccessMask 0x7).
(define fa-privatescope #x0000)
(define fa-private #x0001)
(define fa-famandassem #x0002)
(define fa-assembly #x0003)
(define fa-family #x0004)
(define fa-famorassem #x0005)
(define fa-public #x0006)
(define fa-access-mask #x0007)
(define fa-static #x0010)
(define fa-initonly #x0020)
(define fa-literal #x0040)
(define fa-notserialized #x0080)
(define fa-hasfieldrva #x0100)
(define fa-specialname #x0200)
(define fa-rtspecialname #x0400)
(define fa-hasfieldmarshal #x1000)
(define fa-pinvokeimpl #x2000)
(define fa-hasdefault #x8000)
; Bits that the spec reserves (II.23.1.5); they must be zero in a valid row.
(define fa-reserved-mask #x9500)

; II.23.1.13 ParamAttributes
(define pa-in #x0001)
(define pa-out #x0002)
(define pa-lcid #x0004)
(define pa-retval #x0008)
(define pa-optional #x0010)
(define pa-hasdefault #x1000)
(define pa-hasfieldmarshal #x2000)
(define pa-reserved3 #x4000)
(define pa-reserved4 #x8000)
(define pa-reserved-mask #xF000)

; Access keywords are mutually exclusive. compilercontrolled is the PrivateScope value (0).
(define field-access-keywords
  `((privatescope . ,fa-privatescope) (compilercontrolled . ,fa-privatescope)
    (private . ,fa-private) (famandassem . ,fa-famandassem) (assembly . ,fa-assembly)
    (family . ,fa-family) (famorassem . ,fa-famorassem) (public . ,fa-public)))

(define field-keywords
  `((static . ,fa-static) (initonly . ,fa-initonly) (literal . ,fa-literal)
    (notserialized . ,fa-notserialized) (specialname . ,fa-specialname)
    (rtspecialname . ,fa-rtspecialname)))

(define param-keywords
  `((in . ,pa-in) (out . ,pa-out) (lcid . ,pa-lcid) (retval . ,pa-retval)
    (optional . ,pa-optional) (opt . ,pa-optional)))

; A field's access is 0 (PrivateScope) when no access keyword is given.
(define (field-attributes-flags kws)
  (define access
    (for/list ([k (in-list kws)] #:when (assq k field-access-keywords))
      (cdr (assq k field-access-keywords))))
  (when (> (length access) 1)
    (error 'flags "more than one field access modifier in ~s" kws))
  (for/fold ([acc (if (null? access) 0 (car access))])
            ([k (in-list kws)] #:unless (assq k field-access-keywords))
    (bitwise-ior acc (cond [(assq k field-keywords) => cdr]
                           [else (error 'flags "unsupported field flag ~a" k)]))))

(define (param-attributes-flags kws)
  (for/fold ([acc 0]) ([k (in-list kws)])
    (bitwise-ior acc (cond [(assq k param-keywords) => cdr]
                           [else (error 'flags "unsupported parameter flag ~a" k)]))))

; II.23.1.8 PInvokeAttributes, the MappingFlags column of an ImplMap row (II.22.22).
; charset is 'ansi, 'unicode, 'auto, or #f for NotSpecified. conv is the calling convention keyword.
(define pinvoke-conv-flags
  '((winapi . #x0100) (cdecl . #x0200) (stdcall . #x0300) (thiscall . #x0400) (fastcall . #x0500)))
(define pinvoke-charset-flags
  '((ansi . #x0002) (unicode . #x0004) (auto . #x0006)))
(define pinvoke-supports-last-error #x0040)

(define (pinvoke-attributes-flags conv charset lasterr?)
  (define c (assq conv pinvoke-conv-flags))
  (unless c (error 'flags "unsupported calling convention ~a" conv))
  (bitwise-ior (cdr c)
               (if charset
                   (cdr (or (assq charset pinvoke-charset-flags)
                            (error 'flags "unsupported charset ~a" charset)))
                   0)
               (if lasterr? pinvoke-supports-last-error 0)))

; II.23.1.7 GenericParamAttributes. Only the special constraints are written in source; the
; variance bits (covariant, contravariant) are left zero.
(define gpa-reference-type #x0004)
(define gpa-not-nullable-valuetype #x0008)
(define gpa-default-ctor #x0010)
(define gp-special-keyword-flags
  `((class . ,gpa-reference-type) (valuetype . ,gpa-not-nullable-valuetype)
    (.ctor . ,gpa-default-ctor)))

; specials are the keywords class, valuetype and .ctor (new()) of one type parameter.
(define (generic-param-attributes-flags specials)
  (when (and (memq 'class specials) (memq 'valuetype specials))
    (error 'flags "a type parameter cannot be both class and valuetype"))
  (for/fold ([acc 0]) ([k (in-list specials)])
    (bitwise-ior acc (cond [(assq k gp-special-keyword-flags) => cdr]
                           [else (error 'flags "unsupported generic parameter constraint ~a" k)]))))
