(
  (.assembly extern "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v4.7.1/mscorlib.dll" {})
  (.assembly donothing {})
  (.module ops-eh-filter.exe)
  (.class (private auto ansi) <Module>
    [
     (.method
      (public static) void main () (cil managed)
      {
       (.entrypoint)
       ; Clauses are listed in source order. The inner clause of A comes before the outer catch that
       ; encloses it, because the runtime searches the table in order (II.25.4.6). A filter clause
       ; has Flags 0x0001 and its ClassToken is the offset of its filter block.
       (.try (filter a_filt) a_ts a_te a_hs a_he)
       (.try (catch (mscorlib System.Exception)) a_ots a_ote a_ohs a_ohe)
       (.try (filter b_filt) b_ts b_te b_hs b_he)

       ; A: the filter returns 0, so the inner handler does not run. The exception keeps searching
       ; and the outer catch runs. Expected output: 101 (filter), then 102 (outer catch).
       a_ots:
       a_ts:
       (ldc.i4 1) (ldc.i4.0) (div) (pop)
       (leave a_done)
       a_te:
       a_filt:
       (pop)
       (ldc.i4 101) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.0)
       endfilter
       a_hs:
       (pop)
       (ldc.i4 103) (call void (mscorlib System.Console) WriteLine (int32))
       (leave a_done)
       a_he:
       a_ote:
       a_ohs:
       (pop)
       (ldc.i4 102) (call void (mscorlib System.Console) WriteLine (int32))
       (leave a_done)
       a_ohe:
       a_done:

       ; B: the filter returns 1, so the handler runs. Expected output: 104 (filter), then 105.
       b_ts:
       (ldc.i4 2) (ldc.i4.0) (div) (pop)
       (leave b_done)
       b_te:
       b_filt:
       (pop)
       (ldc.i4 104) (call void (mscorlib System.Console) WriteLine (int32))
       (ldc.i4.1)
       endfilter
       b_hs:
       (pop)
       (ldc.i4 105) (call void (mscorlib System.Console) WriteLine (int32))
       (leave b_done)
       b_he:
       b_done:
       (ret)
       })
     ]))
