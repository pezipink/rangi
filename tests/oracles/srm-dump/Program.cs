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
        if (args.Length != 1)
        {
            Console.Error.WriteLine("usage: srm-dump <image>");
            return 2;
        }

        using var stream = File.OpenRead(args[0]);
        using var pe = new PEReader(stream);
        var md = pe.GetMetadataReader();
        var sb = new StringBuilder();

        DumpModule(md, sb);
        DumpTypeRefs(md, sb);
        DumpTypeDefs(md, sb);
        DumpMethodDefs(pe, md, sb);
        DumpMemberRefs(md, sb);
        DumpAssembly(md, sb);
        DumpAssemblyRefs(md, sb);

        var bytes = Encoding.UTF8.GetBytes(sb.ToString());
        using var stdout = Console.OpenStandardOutput();
        stdout.Write(bytes, 0, bytes.Length);
        return 0;
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
            if (m.RelativeVirtualAddress != 0)
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
}
