(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-eh-finally.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; Clauses are listed in source order. An inner clause comes before the outer clause
       ; that encloses it, because the runtime searches the table in order (II.25.4.6).
       (.try (finally) a_ts a_te a_hs a_he)
       (.try (finally) b_its b_ite b_ihs b_ihe)
       (.try (catch (mscorlib System.Exception)) b_ots b_ote b_ohs b_ohe)
       (.try (fault) c1_ts c1_te c1_hs c1_he)
       (.try (fault) c2_ts c2_te c2_hs c2_he)
       (.try (catch (mscorlib System.Exception)) c_ots c_ote c_ohs c_ohe)

       ; A: finally on normal exit. leave runs the finally, then control leaves the region.
       a_ts:
       (ldc.i4 1) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 2) (call void (mscorlib System.Console) WriteLine (int32))
       (leave a_done)
       a_te:
       a_hs:
       (ldc.i4 3) (call void (mscorlib System.Console) WriteLine (int32))
       endfinally
       a_he:
       a_done:

       ; B: finally runs while an exception unwinds through it, then the outer catch runs.
       b_ots:
       b_its:
       (ldc.i4 4) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 1) (ldc.i4.0) (div) (pop)
       (leave b_in_done)
       b_ite:
       b_ihs:
       (ldc.i4 5) (call void (mscorlib System.Console) WriteLine (int32))
       endfinally
       b_ihe:
       b_in_done:
       (leave b_done)
       b_ote:
       b_ohs:
       (pop)
       (ldc.i4 6) (call void (mscorlib System.Console) WriteLine (int32))
       (leave b_done)
       b_ohe:
       b_done:

       ; C1: fault is not run on normal exit, so 90 must not print.
       c1_ts:
       (ldc.i4 7) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 8) (call void (mscorlib System.Console) WriteLine (int32))
       (leave c1_done)
       c1_te:
       c1_hs:
       (ldc.i4 90) (call void (mscorlib System.Console) WriteLine (int32))
       endfault
       c1_he:
       c1_done:

       ; C2: fault runs while an exception unwinds through it, then the outer catch runs.
       c_ots:
       c2_ts:
       (ldc.i4 9) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4 1) (ldc.i4.0) (div) (pop)
       (leave c2_done)
       c2_te:
       c2_hs:
       (ldc.i4 10) (call void (mscorlib System.Console) WriteLine (int32))
       endfault
       c2_he:
       c2_done:
       (leave c_done)
       c_ote:
       c_ohs:
       (pop)
       (ldc.i4 11) (call void (mscorlib System.Console) WriteLine (int32))
       (leave c_done)
       c_ohe:
       c_done:
       (ret)
       })
     ]))
