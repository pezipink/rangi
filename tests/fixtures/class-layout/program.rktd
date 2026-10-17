; ClassLayout (II.22.8) and FieldLayout (II.22.16) for an explicit and a sequential value type, plus a
; FieldMarshal row (II.22.9, blob II.23.2.6) on one field of the sequential one. Overlay's fields sit
; at byte offsets 0 and 4 with .pack 4 and .size 8. Packed has .pack 2 and .size 12, and its fields
; are laid out in declaration order. Expected stdout: 7, 35, 40, 2.
(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly class-layout {})
  (.module class-layout.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       (.locals init ((valuetype Overlay) (valuetype Packed)))
       ; the explicit struct: lo at offset 0 and hi at offset 4 read back as written: 7, 35
       (ldloca.s 0) (ldc.i4 7) (stfld Overlay lo int32)
       (ldloca.s 0) (ldc.i4 35) (stfld Overlay hi int32)
       (ldloca.s 0) (ldfld Overlay lo int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloca.s 0) (ldfld Overlay hi int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       ; the sequential struct: a and its marshaled field b, read back: 40, 2
       (ldloca.s 1) (ldc.i4 40) (stfld Packed a int32)
       (ldloca.s 1) (ldc.i4 2) (stfld Packed b int32)
       (ldloca.s 1) (ldfld Packed a int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ldloca.s 1) (ldfld Packed b int32)
       (call void (mscorlib System.Console) WriteLine (int32))
       (ret)
       })
     ])
  (.class (public explicit ansi sealed) Overlay
    (.extends (mscorlib System.ValueType))
    [
     (.pack 4)
     (.size 8)
     (.field (public) int32 lo offset 0)
     (.field (public) int32 hi offset 4)
     ])
  (.class (public sequential ansi sealed) Packed
    (.extends (mscorlib System.ValueType))
    [
     (.pack 2)
     (.size 12)
     (.field (public) int32 a)
     (.field (public) (marshal int32) int32 b)
     ]))
