using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text;

internal static class Program
{
    private static int Main(string[] args)
    {
        bool batch = args.Length > 0 && args[0] == "--batch";
        var files = batch ? args.Skip(1).ToArray() : args;
        if (files.Length == 0 || (!batch && files.Length != 1))
        {
            Console.Error.WriteLine("usage: srm-dump <image> | srm-dump --batch <image>...");
            return 2;
        }

        using var stdout = Console.OpenStandardOutput();
        foreach (var file in files)
        {
            if (batch)
            {
                WriteText(stdout, $"=== FILE {file}\n");
                try
                {
                    WriteText(stdout, DumpFile(file));
                }
                catch (Exception ex)
                {
                    WriteText(stdout, "=== ERROR " + ex.Message.ReplaceLineEndings(" ") + "\n");
                }
            }
            else
            {
                WriteText(stdout, DumpFile(file));
            }
        }
        return 0;
    }

    private static string DumpFile(string path)
    {
        using var stream = File.OpenRead(path);
        using var pe = new PEReader(stream);
        var md = pe.GetMetadataReader();
        var raw = new RawTables(pe, md);
        var sb = new StringBuilder();

        DumpModule(md, sb);
        DumpTypeRefs(md, sb);
        DumpTypeDefs(md, sb);
        DumpFields(md, sb);
        DumpMethodDefs(pe, md, sb);
        DumpParams(md, sb);
        DumpInterfaceImpls(md, raw, sb);
        DumpMemberRefs(md, sb);
        DumpConstants(md, sb);
        DumpCustomAttributes(md, sb);
        DumpFieldMarshals(md, raw, sb);
        DumpDeclSecurities(md, sb);
        DumpClassLayouts(raw, sb);
        DumpFieldLayouts(raw, sb);
        DumpStandAloneSigs(md, sb);
        DumpEventMaps(md, raw, sb);
        DumpEvents(md, sb);
        DumpPropertyMaps(md, raw, sb);
        DumpProperties(md, sb);
        DumpMethodSemantics(raw, sb);
        DumpMethodImpls(md, sb);
        DumpModuleRefs(md, sb);
        DumpTypeSpecs(md, sb);
        DumpImplMaps(raw, sb);
        DumpFieldRvas(raw, sb);
        DumpAssembly(md, sb);
        DumpAssemblyRefs(md, sb);
        DumpFiles(raw, sb);
        DumpExportedTypes(raw, sb);
        DumpManifestResources(raw, sb);
        DumpNestedClasses(raw, sb);
        DumpGenericParams(md, sb);
        DumpMethodSpecs(md, sb);
        DumpGenericParamConstraints(md, sb);
        return sb.ToString();
    }

    private static void WriteText(Stream stdout, string text)
    {
        var bytes = Encoding.UTF8.GetBytes(text);
        stdout.Write(bytes, 0, bytes.Length);
    }


    private static void DumpModule(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Module);
        if (n == 0) return;
        var m = md.GetModuleDefinition();
        Header(sb, "Module", n);
        Row(sb, "Module", 1,
            $"Name={Str(md, m.Name)}",
            $"Mvid={md.GetGuid(m.Mvid).ToString("N")}");
    }

    private static void DumpTypeRefs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.TypeRef);
        if (n == 0) return;
        Header(sb, "TypeRef", n);
        for (int i = 1; i <= n; i++)
        {
            var tr = md.GetTypeReference(MetadataTokens.TypeReferenceHandle(i));
            Row(sb, "TypeRef", i,
                $"ResolutionScope={Token(tr.ResolutionScope)}",
                $"Name={Str(md, tr.Name)}",
                $"Namespace={Str(md, tr.Namespace)}");
        }
    }

    private static void DumpTypeDefs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.TypeDef);
        if (n == 0) return;
        Header(sb, "TypeDef", n);
        for (int i = 1; i <= n; i++)
        {
            var td = md.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle(i));
            Row(sb, "TypeDef", i,
                $"Flags={(int)td.Attributes}",
                $"Name={Str(md, td.Name)}",
                $"Namespace={Str(md, td.Namespace)}",
                $"Extends={Token(td.BaseType)}",
                $"Fields={ListRange(td.GetFields().Select(h => MetadataTokens.GetRowNumber((EntityHandle)h)))}",
                $"Methods={ListRange(td.GetMethods().Select(h => MetadataTokens.GetRowNumber((EntityHandle)h)))}");
        }
    }

    private static void DumpMethodDefs(PEReader pe, MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.MethodDef);
        if (n == 0) return;
        Header(sb, "MethodDef", n);
        for (int i = 1; i <= n; i++)
        {
            var m = md.GetMethodDefinition(MetadataTokens.MethodDefinitionHandle(i));
            var fields = new List<string>
            {
                $"Rva={m.RelativeVirtualAddress}",
                $"ImplFlags={(int)m.ImplAttributes}",
                $"Flags={(int)m.Attributes}",
                $"Name={Str(md, m.Name)}",
                $"Signature={BlobHex(md, m.Signature)}",
                $"Params={ListRange(m.GetParameters().Select(h => MetadataTokens.GetRowNumber((EntityHandle)h)))}",
            };
            // II.23.1.10: CodeTypeMask 0x3 == 0 is CIL; native or runtime bodies have no IL to dump.
            if (m.RelativeVirtualAddress != 0 && ((int)m.ImplAttributes & 0x3) == 0)
            {
                fields.Add($"Il={Hex(ReadIl(pe, m.RelativeVirtualAddress))}");
            }
            Row(sb, "MethodDef", i, fields);
        }
    }

    private static void DumpMemberRefs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.MemberRef);
        if (n == 0) return;
        Header(sb, "MemberRef", n);
        for (int i = 1; i <= n; i++)
        {
            var mr = md.GetMemberReference(MetadataTokens.MemberReferenceHandle(i));
            Row(sb, "MemberRef", i,
                $"Parent={Token(mr.Parent)}",
                $"Name={Str(md, mr.Name)}",
                $"Signature={BlobHex(md, mr.Signature)}");
        }
    }

    private static void DumpAssembly(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Assembly);
        if (n == 0) return;
        var a = md.GetAssemblyDefinition();
        Header(sb, "Assembly", n);
        Row(sb, "Assembly", 1,
            $"HashAlgorithm={(int)a.HashAlgorithm}",
            $"Version={Ver(a.Version)}",
            $"Flags={(int)a.Flags}",
            $"PublicKey={BlobHex(md, a.PublicKey)}",
            $"Name={Str(md, a.Name)}",
            $"Culture={Str(md, a.Culture)}");
    }

    private static void DumpAssemblyRefs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.AssemblyRef);
        if (n == 0) return;
        Header(sb, "AssemblyRef", n);
        for (int i = 1; i <= n; i++)
        {
            var ar = md.GetAssemblyReference(MetadataTokens.AssemblyReferenceHandle(i));
            Row(sb, "AssemblyRef", i,
                $"Version={Ver(ar.Version)}",
                $"Flags={(int)ar.Flags}",
                $"PublicKeyOrToken={BlobHex(md, ar.PublicKeyOrToken)}",
                $"Name={Str(md, ar.Name)}",
                $"Culture={Str(md, ar.Culture)}",
                $"HashValue={BlobHex(md, ar.HashValue)}");
        }
    }

    private static void DumpMethodSpecs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.MethodSpec);
        if (n == 0) return;
        Header(sb, "MethodSpec", n);
        for (int i = 1; i <= n; i++)
        {
            var ms = md.GetMethodSpecification(MetadataTokens.MethodSpecificationHandle(i));
            Row(sb, "MethodSpec", i,
                $"Method={Token(ms.Method)}",
                $"Instantiation={BlobHex(md, ms.Signature)}");
        }
    }

    private static void DumpFields(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Field);
        if (n == 0) return;
        Header(sb, "Field", n);
        for (int i = 1; i <= n; i++)
        {
            var f = md.GetFieldDefinition(MetadataTokens.FieldDefinitionHandle(i));
            Row(sb, "Field", i,
                $"Flags={(int)f.Attributes}",
                $"Name={Str(md, f.Name)}",
                $"Signature={BlobHex(md, f.Signature)}");
        }
    }

    private static void DumpParams(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Param);
        if (n == 0) return;
        Header(sb, "Param", n);
        for (int i = 1; i <= n; i++)
        {
            var p = md.GetParameter(MetadataTokens.ParameterHandle(i));
            Row(sb, "Param", i,
                $"Flags={(int)p.Attributes}",
                $"Sequence={p.SequenceNumber}",
                $"Name={Str(md, p.Name)}");
        }
    }

    private static void DumpInterfaceImpls(MetadataReader md, RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.InterfaceImpl);
        if (n == 0) return;
        Header(sb, "InterfaceImpl", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.InterfaceImpl, i);
            long cls = raw.Simple(TableIndex.TypeDef);
            string iface = raw.Coded(2, TableIndex.TypeDef, TableIndex.TypeRef, TableIndex.TypeSpec);
            raw.End();
            Row(sb, "InterfaceImpl", i, $"Class={cls}", $"Interface={iface}");
        }
    }

    private static void DumpConstants(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Constant);
        if (n == 0) return;
        Header(sb, "Constant", n);
        for (int i = 1; i <= n; i++)
        {
            var c = md.GetConstant(MetadataTokens.ConstantHandle(i));
            Row(sb, "Constant", i,
                $"Type={(int)c.TypeCode}",
                $"Parent={Token(c.Parent)}",
                $"Value={BlobHex(md, c.Value)}");
        }
    }

    private static void DumpCustomAttributes(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.CustomAttribute);
        if (n == 0) return;
        Header(sb, "CustomAttribute", n);
        for (int i = 1; i <= n; i++)
        {
            var ca = md.GetCustomAttribute(MetadataTokens.CustomAttributeHandle(i));
            Row(sb, "CustomAttribute", i,
                $"Parent={Token(ca.Parent)}",
                $"Type={Token(ca.Constructor)}",
                $"Value={BlobHex(md, ca.Value)}");
        }
    }

    private static void DumpFieldMarshals(MetadataReader md, RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.FieldMarshal);
        if (n == 0) return;
        Header(sb, "FieldMarshal", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.FieldMarshal, i);
            string parent = raw.Coded(1, TableIndex.Field, TableIndex.Param);
            string nativeType = raw.BlobCol();
            raw.End();
            Row(sb, "FieldMarshal", i, $"Parent={parent}", $"NativeType={nativeType}");
        }
    }

    private static void DumpDeclSecurities(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.DeclSecurity);
        if (n == 0) return;
        Header(sb, "DeclSecurity", n);
        for (int i = 1; i <= n; i++)
        {
            var d = md.GetDeclarativeSecurityAttribute(MetadataTokens.DeclarativeSecurityAttributeHandle(i));
            Row(sb, "DeclSecurity", i,
                $"Action={(int)d.Action}",
                $"Parent={Token(d.Parent)}",
                $"PermissionSet={BlobHex(md, d.PermissionSet)}");
        }
    }

    private static void DumpClassLayouts(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.ClassLayout);
        if (n == 0) return;
        Header(sb, "ClassLayout", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.ClassLayout, i);
            long packing = raw.U(2);
            long classSize = raw.U(4);
            long parent = raw.Simple(TableIndex.TypeDef);
            raw.End();
            Row(sb, "ClassLayout", i,
                $"PackingSize={packing}",
                $"ClassSize={classSize}",
                $"Parent={parent}");
        }
    }

    private static void DumpFieldLayouts(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.FieldLayout);
        if (n == 0) return;
        Header(sb, "FieldLayout", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.FieldLayout, i);
            long offset = raw.U(4);
            long field = raw.Simple(TableIndex.Field);
            raw.End();
            Row(sb, "FieldLayout", i, $"Offset={offset}", $"Field={field}");
        }
    }

    private static void DumpStandAloneSigs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.StandAloneSig);
        if (n == 0) return;
        Header(sb, "StandAloneSig", n);
        for (int i = 1; i <= n; i++)
        {
            var s = md.GetStandaloneSignature(MetadataTokens.StandaloneSignatureHandle(i));
            Row(sb, "StandAloneSig", i, $"Signature={BlobHex(md, s.Signature)}");
        }
    }

    // The EventMap row's list comes from the typed TypeDefinition.GetEvents, so the Racket
    // range computation is checked against SRM's own list resolution.
    private static void DumpEventMaps(MetadataReader md, RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.EventMap);
        if (n == 0) return;
        Header(sb, "EventMap", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.EventMap, i);
            long parent = raw.Simple(TableIndex.TypeDef);
            raw.Simple(TableIndex.Event);
            raw.End();
            var events = md.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle((int)parent)).GetEvents();
            Row(sb, "EventMap", i,
                $"Parent={parent}",
                $"Events={ListRange(events.Select(h => MetadataTokens.GetRowNumber((EntityHandle)h)))}");
        }
    }

    private static void DumpEvents(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Event);
        if (n == 0) return;
        Header(sb, "Event", n);
        for (int i = 1; i <= n; i++)
        {
            var e = md.GetEventDefinition(MetadataTokens.EventDefinitionHandle(i));
            Row(sb, "Event", i,
                $"Flags={(int)e.Attributes}",
                $"Name={Str(md, e.Name)}",
                $"Type={Token(e.Type)}");
        }
    }

    private static void DumpPropertyMaps(MetadataReader md, RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.PropertyMap);
        if (n == 0) return;
        Header(sb, "PropertyMap", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.PropertyMap, i);
            long parent = raw.Simple(TableIndex.TypeDef);
            raw.Simple(TableIndex.Property);
            raw.End();
            var properties = md.GetTypeDefinition(MetadataTokens.TypeDefinitionHandle((int)parent)).GetProperties();
            Row(sb, "PropertyMap", i,
                $"Parent={parent}",
                $"Properties={ListRange(properties.Select(h => MetadataTokens.GetRowNumber((EntityHandle)h)))}");
        }
    }

    private static void DumpProperties(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.Property);
        if (n == 0) return;
        Header(sb, "Property", n);
        for (int i = 1; i <= n; i++)
        {
            var p = md.GetPropertyDefinition(MetadataTokens.PropertyDefinitionHandle(i));
            Row(sb, "Property", i,
                $"Flags={(int)p.Attributes}",
                $"Name={Str(md, p.Name)}",
                $"Type={BlobHex(md, p.Signature)}");
        }
    }

    private static void DumpMethodSemantics(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.MethodSemantics);
        if (n == 0) return;
        Header(sb, "MethodSemantics", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.MethodSemantics, i);
            long semantics = raw.U(2);
            long method = raw.Simple(TableIndex.MethodDef);
            string association = raw.Coded(1, TableIndex.Event, TableIndex.Property);
            raw.End();
            Row(sb, "MethodSemantics", i,
                $"Semantics={semantics}",
                $"Method={method}",
                $"Association={association}");
        }
    }

    private static void DumpMethodImpls(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.MethodImpl);
        if (n == 0) return;
        Header(sb, "MethodImpl", n);
        for (int i = 1; i <= n; i++)
        {
            var mi = md.GetMethodImplementation(MetadataTokens.MethodImplementationHandle(i));
            Row(sb, "MethodImpl", i,
                $"Class={MetadataTokens.GetRowNumber((EntityHandle)mi.Type)}",
                $"Body={Token(mi.MethodBody)}",
                $"Declaration={Token(mi.MethodDeclaration)}");
        }
    }

    private static void DumpModuleRefs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.ModuleRef);
        if (n == 0) return;
        Header(sb, "ModuleRef", n);
        for (int i = 1; i <= n; i++)
        {
            var mr = md.GetModuleReference(MetadataTokens.ModuleReferenceHandle(i));
            Row(sb, "ModuleRef", i, $"Name={Str(md, mr.Name)}");
        }
    }

    private static void DumpTypeSpecs(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.TypeSpec);
        if (n == 0) return;
        Header(sb, "TypeSpec", n);
        for (int i = 1; i <= n; i++)
        {
            var ts = md.GetTypeSpecification(MetadataTokens.TypeSpecificationHandle(i));
            Row(sb, "TypeSpec", i, $"Signature={BlobHex(md, ts.Signature)}");
        }
    }

    private static void DumpImplMaps(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.ImplMap);
        if (n == 0) return;
        Header(sb, "ImplMap", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.ImplMap, i);
            long flags = raw.U(2);
            string memberForwarded = raw.Coded(1, TableIndex.Field, TableIndex.MethodDef);
            string importName = raw.StrCol();
            long importScope = raw.Simple(TableIndex.ModuleRef);
            raw.End();
            Row(sb, "ImplMap", i,
                $"Flags={flags}",
                $"MemberForwarded={memberForwarded}",
                $"ImportName={importName}",
                $"ImportScope={importScope}");
        }
    }

    private static void DumpFieldRvas(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.FieldRva);
        if (n == 0) return;
        Header(sb, "FieldRva", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.FieldRva, i);
            long rva = raw.U(4);
            long field = raw.Simple(TableIndex.Field);
            raw.End();
            Row(sb, "FieldRva", i, $"Rva={rva}", $"Field={field}");
        }
    }

    private static void DumpFiles(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.File);
        if (n == 0) return;
        Header(sb, "File", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.File, i);
            long flags = raw.U(4);
            string name = raw.StrCol();
            string hash = raw.BlobCol();
            raw.End();
            Row(sb, "File", i, $"Flags={flags}", $"Name={name}", $"HashValue={hash}");
        }
    }

    private static void DumpExportedTypes(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.ExportedType);
        if (n == 0) return;
        Header(sb, "ExportedType", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.ExportedType, i);
            long flags = raw.U(4);
            long typeDefId = raw.U(4);
            string name = raw.StrCol();
            string ns = raw.StrCol();
            string implementation = raw.Coded(2, TableIndex.File, TableIndex.AssemblyRef, TableIndex.ExportedType);
            raw.End();
            Row(sb, "ExportedType", i,
                $"Flags={flags}",
                $"TypeDefId={typeDefId}",
                $"Name={name}",
                $"Namespace={ns}",
                $"Implementation={implementation}");
        }
    }

    private static void DumpManifestResources(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.ManifestResource);
        if (n == 0) return;
        Header(sb, "ManifestResource", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.ManifestResource, i);
            long offset = raw.U(4);
            long flags = raw.U(4);
            string name = raw.StrCol();
            string implementation = raw.Coded(2, TableIndex.File, TableIndex.AssemblyRef, TableIndex.ExportedType);
            raw.End();
            Row(sb, "ManifestResource", i,
                $"Offset={offset}",
                $"Flags={flags}",
                $"Name={name}",
                $"Implementation={implementation}");
        }
    }

    private static void DumpNestedClasses(RawTables raw, StringBuilder sb)
    {
        int n = raw.Rows(TableIndex.NestedClass);
        if (n == 0) return;
        Header(sb, "NestedClass", n);
        for (int i = 1; i <= n; i++)
        {
            raw.Begin(TableIndex.NestedClass, i);
            long nested = raw.Simple(TableIndex.TypeDef);
            long enclosing = raw.Simple(TableIndex.TypeDef);
            raw.End();
            Row(sb, "NestedClass", i, $"Nested={nested}", $"Enclosing={enclosing}");
        }
    }

    private static void DumpGenericParams(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.GenericParam);
        if (n == 0) return;
        Header(sb, "GenericParam", n);
        for (int i = 1; i <= n; i++)
        {
            var gp = md.GetGenericParameter(MetadataTokens.GenericParameterHandle(i));
            Row(sb, "GenericParam", i,
                $"Number={gp.Index}",
                $"Flags={(int)gp.Attributes}",
                $"Owner={Token(gp.Parent)}",
                $"Name={Str(md, gp.Name)}");
        }
    }

    private static void DumpGenericParamConstraints(MetadataReader md, StringBuilder sb)
    {
        int n = md.GetTableRowCount(TableIndex.GenericParamConstraint);
        if (n == 0) return;
        Header(sb, "GenericParamConstraint", n);
        for (int i = 1; i <= n; i++)
        {
            var c = md.GetGenericParameterConstraint(MetadataTokens.GenericParameterConstraintHandle(i));
            Row(sb, "GenericParamConstraint", i,
                $"Owner={MetadataTokens.GetRowNumber((EntityHandle)c.Parameter)}",
                $"Constraint={Token(c.Type)}");
        }
    }

    private static byte[] ReadIl(PEReader pe, int rva)
    {
        var reader = pe.GetSectionData(rva).GetReader();
        return MethodBodyBlock.Create(reader).GetILBytes();
    }

    private static void Header(StringBuilder sb, string table, int count)
    {
        sb.Append(table).Append(" rows=").Append(count).Append('\n');
    }

    private static void Row(StringBuilder sb, string table, int index, params string[] fields)
    {
        Row(sb, table, index, (IEnumerable<string>)fields);
    }

    private static void Row(StringBuilder sb, string table, int index, IEnumerable<string> fields)
    {
        sb.Append("  ").Append(table).Append('[').Append(index).Append("] ")
          .Append(string.Join(" ", fields)).Append('\n');
    }

    private static string Str(MetadataReader md, StringHandle h)
    {
        return "\"" + (h.IsNil ? "" : md.GetString(h)) + "\"";
    }

    private static string Token(EntityHandle h)
    {
        return h.IsNil ? "0x00000000" : $"0x{MetadataTokens.GetToken(h):x8}";
    }

    private static string BlobHex(MetadataReader md, BlobHandle h)
    {
        return h.IsNil ? "" : Hex(md.GetBlobBytes(h));
    }

    private static string Hex(byte[] bytes)
    {
        return Convert.ToHexString(bytes).ToLowerInvariant();
    }

    private static string Ver(Version v)
    {
        return $"{v.Major}.{v.Minor}.{v.Build}.{v.Revision}";
    }

    private static string ListRange(IEnumerable<int> rows)
    {
        int first = -1, last = -1;
        foreach (var r in rows)
        {
            if (first < 0) first = r;
            last = r;
        }
        return first < 0 ? "[]" : $"[{first}..{last}]";
    }

    // Reads table rows column by column, for tables whose columns SRM's typed API does not expose.
    // Offsets come from SRM's table layout; column widths are derived here from the #~ HeapSizes
    // byte and row counts (II.24.2.6), so the row-size check in End() validates the layout.
    private sealed class RawTables
    {
        private readonly byte[] _block;
        private readonly MetadataReader _md;
        private readonly bool _wideStrings;
        private readonly bool _wideBlobs;
        private TableIndex _table;
        private int _start;
        private int _pos;

        public RawTables(PEReader pe, MetadataReader md)
        {
            _block = pe.GetMetadata().GetContent().ToArray();
            _md = md;
            int heapSizes = _block[StreamOffset("#~", "#-") + 6];
            _wideStrings = (heapSizes & 0x1) != 0;
            _wideBlobs = (heapSizes & 0x4) != 0;
        }

        public int Rows(TableIndex t) => _md.GetTableRowCount(t);

        public void Begin(TableIndex table, int row)
        {
            _table = table;
            _start = _md.GetTableMetadataOffset(table) + (row - 1) * _md.GetTableRowSize(table);
            _pos = _start;
        }

        public void End()
        {
            int consumed = _pos - _start;
            int expected = _md.GetTableRowSize(_table);
            if (consumed != expected)
            {
                throw new InvalidDataException($"{_table} row consumed {consumed} bytes, expected {expected}");
            }
        }

        public long U(int n)
        {
            long v = 0;
            for (int i = 0; i < n; i++)
            {
                v |= (long)_block[_pos + i] << (8 * i);
            }
            _pos += n;
            return v;
        }

        // II.24.2.6: simple index is 2 bytes unless the target table has 2^16 or more rows
        public long Simple(TableIndex t) => U(_md.GetTableRowCount(t) < 0x10000 ? 2 : 4);

        // II.24.2.6: coded index is 2 bytes when every target fits in 16 - bits row bits
        public string Coded(int bits, params TableIndex[] tags)
        {
            int max = 0;
            foreach (var t in tags)
            {
                max = Math.Max(max, _md.GetTableRowCount(t));
            }
            long v = U(max < (1 << (16 - bits)) ? 2 : 4);
            long row = v >> bits;
            if (row == 0)
            {
                return "0x00000000";
            }
            int tag = (int)(v & ((1 << bits) - 1));
            return $"0x{((int)tags[tag] << 24) | (int)row:x8}";
        }

        public string StrCol()
        {
            return Str(_md, MetadataTokens.StringHandle((int)U(_wideStrings ? 4 : 2)));
        }

        public string BlobCol()
        {
            return BlobHex(_md, MetadataTokens.BlobHandle((int)U(_wideBlobs ? 4 : 2)));
        }

        // II.24.2.2: stream headers follow the metadata root; the #~ (or uncompressed #-) header is at the stream offset
        private int StreamOffset(params string[] names)
        {
            int versionLength = BitConverter.ToInt32(_block, 12);
            int p = 16 + versionLength + 2;
            int count = BitConverter.ToUInt16(_block, p);
            p += 2;
            for (int s = 0; s < count; s++)
            {
                int offset = BitConverter.ToInt32(_block, p);
                int nameStart = p + 8;
                int nameEnd = Array.IndexOf(_block, (byte)0, nameStart);
                int nameLength = nameEnd - nameStart;
                if (Array.IndexOf(names, Encoding.ASCII.GetString(_block, nameStart, nameLength)) >= 0)
                {
                    return offset;
                }
                p = nameStart + ((nameLength + 1 + 3) & ~3);
            }
            throw new InvalidDataException($"metadata stream {string.Join(" or ", names)} not found");
        }
    }
}
