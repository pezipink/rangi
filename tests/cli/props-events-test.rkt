#lang racket/base
; Properties and events (II.22.34 Property, II.22.35 PropertyMap, II.22.13 Event, II.22.12
; EventMap, II.22.28 MethodSemantics, II.23.2.5 PropertySig). A property names its getter and
; setter, and an event names its add and remove methods, all in the class body. Accessors get
; SpecialName (0x0800).
(require rackunit
         racket/list
         "../../src/ilasm/syntax.rkt"
         "../../src/cli/lower.rkt"
         "../../src/cli/build.rkt"
         "../../src/cli/reader.rkt"
         "../../src/pe/model.rkt")

(define mscorlib-path
  "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll")

(define (program . classes)
  `((.assembly extern ,mscorlib-path {})
    (.assembly props-events-tests {})
    (.module local.exe)
    (.class (private auto ansi) <Module>
      [(.method (public static) void main () (cil managed) { (.entrypoint) (.maxstack 8) (ret) })])
    ,@classes))

(define (lower . classes)
  (lower-module (parse-il (apply program classes))))

(define (parse . classes)
  (parse-il (apply program classes)))

(define (pe p) (cli-program-propevents p))

(define base-ctor
  '(.method (public specialname rtspecialname) void .ctor () (cil managed)
     { (.maxstack 8) (ldarg.0) (call void (mscorlib System.Object) .ctor ()) (ret) }))

(define (int-getter name)
  `(.method (public) int32 ,name () (cil managed) { (.maxstack 8) (ldc.i4.4) (ret) }))

(define (static-int-getter name)
  `(.method (public static) int32 ,name () (cil managed) { (.maxstack 8) (ldc.i4.4) (ret) }))

(define (void-method name)
  `(.method (public) void ,name () (cil managed) { (.maxstack 8) (ret) }))

(define (box-class name . members)
  `(.class (public auto ansi) ,name
     (.extends (mscorlib System.Object))
     [,base-ctor ,@members]))

(define value-property
  '(.property instance int32 Value () (getter get_Value) (setter set_Value)))

(define box-with-property
  (box-class 'Box (int-getter 'get_Value) (void-method 'set_Value) value-property))

(define (rid-of p name)
  (add1 (index-of (map tdef-name (cli-program-typedefs p)) name)))

(define (method-rid p name)
  (define all (append-map tdef-methods (cli-program-typedefs p)))
  (add1 (index-where all (λ (m) (equal? (mdef-name m) name)))))

(define (method-named p tname name)
  (define td (findf (λ (td) (equal? (tdef-name td) tname)) (cli-program-typedefs p)))
  (findf (λ (m) (equal? (mdef-name m) name)) (tdef-methods td)))

(define specialname-bit #x800)
(define (special? flags) (not (zero? (bitwise-and flags specialname-bit))))

(test-case "an instance property lowers to a PropertyMap and a Property with a HASTHIS PropertySig"
  (define p (lower box-with-property))
  (check-equal? (propevents-propmaps (pe p)) (list (cons (rid-of p "Box") 1)))
  (define props (propevents-props (pe p)))
  (check-equal? (length props) 1)
  (check-equal? (propdef-name (car props)) "Value")
  (check-equal? (propdef-flags (car props)) 0)
  ; PROPERTY | HASTHIS (0x28), ParamCount 0, Type int32 (0x08) (II.23.2.5)
  (check-equal? (propdef-sig (car props)) (bytes #x28 #x00 #x08)))

(test-case "a static property's PropertySig has no HASTHIS bit"
  (define p (lower (box-class 'Box (static-int-getter 'get_Value)
                              '(.property int32 Value () (getter get_Value)))))
  (check-equal? (propdef-sig (car (propevents-props (pe p)))) (bytes #x08 #x00 #x08)))

(test-case "getter and setter get MethodSemantics rows, in source order, linked to the property"
  (define p (lower box-with-property))
  (define sems (propevents-semantics (pe p)))
  (check-equal? (length sems) 2)
  (check-equal? (methodsem-kind (car sems)) #x0002)
  (check-equal? (methodsem-method (car sems)) (method-rid p "get_Value"))
  (check-equal? (methodsem-association (car sems)) (cons 'property 1))
  (check-equal? (methodsem-kind (cadr sems)) #x0001)
  (check-equal? (methodsem-method (cadr sems)) (method-rid p "set_Value"))
  (check-equal? (methodsem-association (cadr sems)) (cons 'property 1)))

(test-case "accessors get SpecialName and other methods do not (II.22.26)"
  (define p (lower (box-class 'Box (int-getter 'get_Value) (void-method 'set_Value)
                              (int-getter 'Plain) value-property)))
  (check-true (special? (mdef-flags (method-named p "Box" "get_Value"))))
  (check-true (special? (mdef-flags (method-named p "Box" "set_Value"))))
  (check-false (special? (mdef-flags (method-named p "Box" "Plain")))))

(test-case "a class with no properties or events has no property rows"
  (define p (lower (box-class 'Box (int-getter 'Plain))))
  (check-equal? (propevents-propmaps (pe p)) '())
  (check-equal? (propevents-props (pe p)) '())
  (check-equal? (propevents-semantics (pe p)) '()))

(define event-box
  (box-class 'Box (void-method 'add_OnChange) (void-method 'remove_OnChange)
             '(.event (mscorlib System.EventHandler) OnChange (add add_OnChange)
                      (remove remove_OnChange))))

(test-case "an event lowers to an EventMap and an Event whose type is a TypeRef"
  (define p (lower event-box))
  (check-equal? (propevents-eventmaps (pe p)) (list (cons (rid-of p "Box") 1)))
  (define evs (propevents-events (pe p)))
  (check-equal? (length evs) 1)
  (check-equal? (evdef-name (car evs)) "OnChange")
  (check-equal? (evdef-flags (car evs)) 0)
  (check-equal? (car (evdef-type (car evs))) 'typeref))

(test-case "an event's add and remove get MethodSemantics rows (II.22.28)"
  (define p (lower event-box))
  (define sems (propevents-semantics (pe p)))
  (check-equal? (map methodsem-kind sems) '(#x0008 #x0010))
  (check-equal? (map methodsem-method sems)
                (list (method-rid p "add_OnChange") (method-rid p "remove_OnChange")))
  (check-equal? (map methodsem-association sems) '((event . 1) (event . 1))))

(test-case "an event with a same-module type lowers to a TypeDef type"
  (define p (lower (box-class 'Box (void-method 'add_OnChange) (void-method 'remove_OnChange)
                              '(.event Box OnChange (add add_OnChange) (remove remove_OnChange)))))
  (check-equal? (evdef-type (car (propevents-events (pe p)))) (cons 'typedef (rid-of p "Box"))))

(test-case "property rows are numbered across classes, one PropertyMap per class with members"
  (define p (lower box-with-property
                   (box-class 'Plain (int-getter 'Plain))
                   (box-class 'Other (int-getter 'get_Other) (void-method 'set_Other)
                              '(.property instance int32 Other () (getter get_Other)
                                          (setter set_Other)))))
  (check-equal? (propevents-propmaps (pe p))
                (list (cons (rid-of p "Box") 1) (cons (rid-of p "Other") 2)))
  (check-equal? (map propdef-name (propevents-props (pe p))) '("Value" "Other"))
  (check-equal? (map methodsem-association (propevents-semantics (pe p)))
                '((property . 1) (property . 1) (property . 2) (property . 2))))

(test-case "property and event rows read back through read-row from built metadata"
  (define p (lower box-with-property
                   (box-class 'Ev (void-method 'add_OnChange) (void-method 'remove_OnChange)
                              '(.event (mscorlib System.EventHandler) OnChange
                                       (add add_OnChange) (remove remove_OnChange)))))
  (define rdr (read-metadata-root (chunk-bytes (build-metadata p "rangi-test" "rangi.dll"))))
  (define pm (read-row rdr 'propertymap 1))
  (check-equal? (vector-ref pm 0) (rid-of p "Box"))
  (check-equal? (vector-ref (read-row rdr 'property 1) 1) "Value")
  (define em (read-row rdr 'eventmap 1))
  (check-equal? (vector-ref em 0) (rid-of p "Ev"))
  (check-equal? (vector-ref (read-row rdr 'event 1) 1) "OnChange")
  (define ms-rows
    (for/list ([i (in-range 1 5)]) (read-row rdr 'methodsemantics i)))
  (define add-row
    (findf (lambda (r) (equal? (vector-ref r 2) (cons 'event 1))) ms-rows))
  (check-equal? (vector-ref add-row 0) #x0008)
  (check-equal? (vector-ref add-row 1) (method-rid p "add_OnChange")))

(define (check-rejected pattern . classes)
  (check-exn pattern (λ () (apply parse classes))))

(test-case "an accessor that names no method is rejected"
  (check-rejected #rx"names no method"
                  (box-class 'Box (int-getter 'get_Value)
                             '(.property instance int32 Value () (getter Missing)))))

(test-case "a duplicate accessor kind is rejected"
  (check-rejected #rx"duplicate property accessor"
                  (box-class 'Box (int-getter 'get_Value) (int-getter 'get_Other)
                             '(.property instance int32 Value () (getter get_Value) (getter get_Other)))))

(test-case "one method used for two accessors is rejected"
  (check-rejected #rx"used by two accessors"
                  (box-class 'Box (int-getter 'get_Value)
                             '(.property instance int32 Value () (getter get_Value) (setter get_Value)))))

(test-case "an overloaded accessor method is rejected"
  (check-rejected #rx"is overloaded"
                  (box-class 'Box (int-getter 'get_Value)
                             `(.method (public) int32 get_Value (int32) (cil managed)
                                { (.maxstack 8) (ldc.i4.4) (ret) })
                             '(.property instance int32 Value () (getter get_Value)))))

(test-case "an accessor of the wrong kind for an event is rejected"
  (check-rejected #rx"getter is not a event accessor"
                  (box-class 'Box (void-method 'add_OnChange)
                             '(.event (mscorlib System.EventHandler) OnChange
                                      (getter add_OnChange)))))

(test-case "an instance property with a static accessor is rejected"
  (check-rejected #rx"instance property Box.Value has static accessor get_Value"
                  (box-class 'Box (static-int-getter 'get_Value)
                             '(.property instance int32 Value () (getter get_Value)))))

(test-case "a static property with an instance accessor is rejected"
  (check-rejected #rx"static property Box.Value has instance accessor get_Value"
                  (box-class 'Box (int-getter 'get_Value)
                             '(.property int32 Value () (getter get_Value)))))

(test-case "a void property is rejected"
  (check-rejected #rx"property Box.Value cannot be void"
                  (box-class 'Box (void-method 'get_Value)
                             '(.property instance void Value () (getter get_Value)))))

(test-case "duplicate property names are rejected"
  (check-rejected #rx"duplicate property Value"
                  (box-class 'Box (int-getter 'get_Value) (int-getter 'get_Other)
                             '(.property instance int32 Value () (getter get_Value))
                             '(.property instance int32 Value () (getter get_Other)))))

(test-case "a malformed accessor is rejected"
  (check-rejected #rx"malformed property accessor"
                  (box-class 'Box (int-getter 'get_Value)
                             '(.property instance int32 Value () (getter)))))
