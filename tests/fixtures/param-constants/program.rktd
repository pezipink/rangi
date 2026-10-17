; Named parameters (II.22.33) with ParameterAttributes and Sequence numbers, and default values
; (Constant rows, II.22.9, blob II.23.1.15) on two of them. The first parameter of Add is unnamed,
; so it gets no Param row, but the named ones keep their parameter positions 2 and 3. Wide's
; default is an int8. Calc.Limit is a literal field, so it gets a Constant row and fdHasDefault
; (II.23.1.5). Expected stdout: 103, 42, 9.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly param-constants {})
  (.module param-constants.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; Add(100, 1, 2): the first argument plus the two named ones: 103
       (ldc.i 100) (ldc.i 1) (ldc.i 2)
       (call int32 (Calc) Add (int32 int32 int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Add(0, 40, 2): 42
       (ldc.i 0) (ldc.i 40) (ldc.i 2)
       (call int32 (Calc) Add (int32 int32 int32))
       (call void (mscorlib System.Console) WriteLine (int32))
       ; Wide(9) returns its argument: 9
       (ldc.i 9)
       (call int32 (Calc) Wide (int8))
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public auto ansi) Calc
    [
     (.field (public static literal) int32 Limit = (int32 42))
     (.method (public static) int32 Add (int32 (param (in) int32 a) (param (opt) int32 b = (int32 5)))
      (cil managed)
      {
       (.maxstack 8)
       (ldarg.1)
       (ldarg.2)
       (add)
       (ldarg.0)
       (add)
       (ret)
       })
     (.method (public static) int32 Wide ((param (opt) int8 w = (int8 -3))) (cil managed)
      {
       (.maxstack 8)
       (ldarg.0)
       (ret)
       })
     ]))
