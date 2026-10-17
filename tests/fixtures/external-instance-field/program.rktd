(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly external-instance-field {})
  (.module external-instance-field.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       (.maxstack 8)
       ; a Header built with its public (string, object) constructor; the stack keeps it at the top
       (ldstr "first")
       (ldstr "value")
       (newobj (mscorlib System.Runtime.Remoting.Messaging.Header) (string object))
       ; ldfld reads Name, which the constructor set: first
       (dup)
       (ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) Name string)
       (call void (mscorlib System.Console) WriteLine (string))
       ; stfld writes Name; ldflda gives a managed pointer to it, read back with ldind.ref: second
       (dup)
       (ldstr "second")
       (stfld (mscorlib System.Runtime.Remoting.Messaging.Header) Name string)
       (dup)
       (ldflda (mscorlib System.Runtime.Remoting.Messaging.Header) Name string)
       (ldind.ref)
       (call void (mscorlib System.Console) WriteLine (string))
       ; a bool field written then read: True
       (dup)
       (ldc.i4.1)
       (stfld (mscorlib System.Runtime.Remoting.Messaging.Header) MustUnderstand boolean)
       (dup)
       (ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) MustUnderstand boolean)
       (call void (mscorlib System.Console) WriteLine (boolean))
       ; the object field, set by the constructor, consumes the header: value
       (ldfld (mscorlib System.Runtime.Remoting.Messaging.Header) Value object)
       (call void (mscorlib System.Console) WriteLine (object))
       (ret)
       })
     ]))
