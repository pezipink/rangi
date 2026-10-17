using System;
using System.Collections.Generic;
using System.IO;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using ILVerify;

namespace ILVerifyOracle
{
    // Runs Microsoft.ILVerification over one image. Usage: ilverify <image> <reference-dir>.
    // Prints one line per verification error and exits 1 if there are any, 0 if the image is clean,
    // 2 if the image or a referenced assembly cannot be read.
    internal static class Program
    {
        private const string SystemModule = "mscorlib";

        public static int Main(string[] args)
        {
            if (args.Length != 2)
            {
                Console.Error.WriteLine("usage: ilverify <image> <reference-dir>");
                return 2;
            }

            try
            {
                return Verify(args[0], args[1]);
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine("ilverify: " + ex.Message);
                return 2;
            }
        }

        private static int Verify(string imagePath, string referenceDir)
        {
            using (PEReader image = new PEReader(File.OpenRead(imagePath)))
            using (DirectoryResolver resolver = new DirectoryResolver(referenceDir))
            {
                MetadataReader metadata = image.GetMetadataReader();
                Verifier verifier = new Verifier(resolver);
                verifier.SetSystemModuleName(new AssemblyNameInfo(SystemModule));

                int errors = 0;
                foreach (VerificationResult result in verifier.Verify(image))
                {
                    errors++;
                    Console.WriteLine(Locate(metadata, result) + ": " + result.Code + ": " + result.Message);
                }

                Console.WriteLine(errors == 0 ? "ILVerify: no errors" : "ILVerify: " + errors + " error(s)");
                return errors == 0 ? 0 : 1;
            }
        }

        private static string Locate(MetadataReader metadata, VerificationResult result)
        {
            if (!result.Method.IsNil)
            {
                MethodDefinition method = metadata.GetMethodDefinition(result.Method);
                return "method " + metadata.GetString(method.Name)
                    + " token 0x" + MetadataTokens.GetToken(result.Method).ToString("X8");
            }
            if (!result.Type.IsNil)
            {
                TypeDefinition type = metadata.GetTypeDefinition(result.Type);
                return "type " + metadata.GetString(type.Name)
                    + " token 0x" + MetadataTokens.GetToken(result.Type).ToString("X8");
            }
            return "module";
        }

        // Resolves references by simple name from one directory, as the reference assemblies are laid out.
        private sealed class DirectoryResolver : IResolver, IDisposable
        {
            private readonly string _directory;
            private readonly Dictionary<string, PEReader> _readers =
                new Dictionary<string, PEReader>(StringComparer.OrdinalIgnoreCase);

            public DirectoryResolver(string directory)
            {
                _directory = directory;
            }

            public PEReader ResolveAssembly(AssemblyNameInfo assemblyName)
            {
                return Open(assemblyName.Name + ".dll");
            }

            public PEReader ResolveModule(AssemblyNameInfo referencingModule, string fileName)
            {
                return Open(fileName);
            }

            private PEReader Open(string fileName)
            {
                string path = Path.Combine(_directory, fileName);
                if (!_readers.TryGetValue(path, out PEReader reader))
                {
                    reader = new PEReader(File.OpenRead(path));
                    _readers.Add(path, reader);
                }
                return reader;
            }

            public void Dispose()
            {
                foreach (PEReader reader in _readers.Values)
                {
                    reader.Dispose();
                }
            }
        }
    }
}
