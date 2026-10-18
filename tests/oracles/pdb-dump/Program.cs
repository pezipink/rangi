using System;
using System.IO;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text;

// Dumps a standalone portable PDB through System.Reflection.Metadata, one line per fact, so
// the Racket tests can compare what SRM decodes with what the writer meant to write. Given an
// image (.exe or .dll) it dumps the debug directory and whether SRM associates the PDB beside it.
internal static class Program
{
    private static int Main(string[] args)
    {
        if (args.Length != 1)
        {
            Console.Error.WriteLine("usage: pdb-dump <pdb | image>");
            return 2;
        }

        if (args[0].EndsWith(".exe", StringComparison.OrdinalIgnoreCase)
            || args[0].EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
        {
            return DumpImage(args[0]);
        }

        using var stream = File.OpenRead(args[0]);
        using var provider = MetadataReaderProvider.FromPortablePdbStream(stream, MetadataStreamOptions.Default);
        var md = provider.GetMetadataReader();
        var sb = new StringBuilder();

        sb.Append("version ").Append(md.MetadataVersion).Append('\n');
        sb.Append("id ").Append(Hex(md.DebugMetadataHeader.Id)).Append('\n');

        var entry = md.DebugMetadataHeader.EntryPoint;
        sb.Append("entry ").Append(entry.IsNil ? "0" : "0x" + MetadataTokens.GetToken(entry).ToString("X8")).Append('\n');

        int documents = md.GetTableRowCount(TableIndex.Document);
        for (int i = 1; i <= documents; i++)
        {
            var doc = md.GetDocument(MetadataTokens.DocumentHandle(i));
            sb.Append("doc ").Append(i).Append(' ').Append(DocName(md, doc.Name)).Append('\n');
        }

        int methods = md.GetTableRowCount(TableIndex.MethodDebugInformation);
        for (int i = 1; i <= methods; i++)
        {
            var handle = MetadataTokens.MethodDebugInformationHandle(i);
            var info = md.GetMethodDebugInformation(handle);
            sb.Append("method ").Append(i).Append(" doc ")
              .Append(info.Document.IsNil ? "nil" : MetadataTokens.GetRowNumber(info.Document).ToString())
              .Append(" localsig ")
              .Append(info.LocalSignature.IsNil ? "0" : MetadataTokens.GetRowNumber(info.LocalSignature).ToString())
              .Append('\n');

            foreach (var sp in info.GetSequencePoints())
            {
                sb.Append("sp ").Append(sp.Offset).Append(' ')
                  .Append(sp.StartLine).Append(' ').Append(sp.StartColumn).Append(' ')
                  .Append(sp.EndLine).Append(' ').Append(sp.EndColumn).Append(' ')
                  .Append(MetadataTokens.GetRowNumber(sp.Document)).Append('\n');
            }

            foreach (var sh in md.GetLocalScopes(handle))
            {
                var scope = md.GetLocalScope(sh);
                sb.Append("scope ").Append(scope.StartOffset).Append(' ').Append(scope.Length).Append('\n');
                foreach (var vh in scope.GetLocalVariables())
                {
                    var v = md.GetLocalVariable(vh);
                    sb.Append("local ").Append(v.Index).Append(' ')
                      .Append(md.GetString(v.Name)).Append('\n');
                }
            }
        }

        var stdout = Console.OpenStandardOutput();
        var bytes = Encoding.UTF8.GetBytes(sb.ToString());
        stdout.Write(bytes, 0, bytes.Length);
        stdout.Flush();
        return 0;
    }

    // The document name blob: a separator character (0 for none), then the UTF-8 parts as
    // compressed #Blob indexes (PortablePdb-Metadata.md, Document Name Blob).
    private static string DocName(MetadataReader md, BlobHandle name)
    {
        var reader = md.GetBlobReader(name);
        char separator = (char)reader.ReadByte();
        var parts = new StringBuilder();
        while (reader.RemainingBytes > 0)
        {
            int index = reader.ReadCompressedInteger();
            if (parts.Length > 0 && separator != '\0')
            {
                parts.Append(separator);
            }
            parts.Append(Encoding.UTF8.GetString(md.GetBlobBytes(MetadataTokens.BlobHandle(index))));
        }
        return parts.ToString();
    }

    // The debug directory of an image, and whether SRM associates the PDB beside it. The
    // association check compares the CodeView GUID and stamp with the PDB Id and verifies the checksum.
    private static int DumpImage(string path)
    {
        using var stream = File.OpenRead(path);
        using var pe = new PEReader(stream);
        var sb = new StringBuilder();

        foreach (var e in pe.ReadDebugDirectory())
        {
            sb.Append("debug type ").Append((int)e.Type)
              .Append(" version ").Append(e.MajorVersion).Append('.').Append(e.MinorVersion)
              .Append(" stamp 0x").Append(e.Stamp.ToString("X8"))
              .Append(" size ").Append(e.DataSize).Append('\n');
            if (e.Type == DebugDirectoryEntryType.CodeView)
            {
                var cv = pe.ReadCodeViewDebugDirectoryData(e);
                sb.Append("codeview guid ").Append(cv.Guid.ToString("N"))
                  .Append(" age ").Append(cv.Age)
                  .Append(" path ").Append(cv.Path).Append('\n');
            }
            else if (e.Type == DebugDirectoryEntryType.PdbChecksum)
            {
                var ck = pe.ReadPdbChecksumDebugDirectoryData(e);
                sb.Append("checksum ").Append(ck.AlgorithmName).Append(' ').Append(Hex(ck.Checksum)).Append('\n');
            }
        }

        bool associated = pe.TryOpenAssociatedPortablePdb(path, File.OpenRead, out var provider, out var pdbPath);
        sb.Append("associated ").Append(associated ? "true" : "false").Append('\n');
        if (associated)
        {
            sb.Append("associated path ").Append(Path.GetFileName(pdbPath)).Append('\n');
            provider.Dispose();
        }

        var stdout = Console.OpenStandardOutput();
        var bytes = Encoding.UTF8.GetBytes(sb.ToString());
        stdout.Write(bytes, 0, bytes.Length);
        stdout.Flush();
        return 0;
    }

    private static string Hex(System.Collections.Immutable.ImmutableArray<byte> bytes)
    {
        var sb = new StringBuilder();
        foreach (var b in bytes)
        {
            sb.Append(b.ToString("x2"));
        }
        return sb.ToString();
    }
}
