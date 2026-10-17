using System;
using System.Linq;
using System.IO;
using System.Reflection;
using System.Reflection.Emit;
using System.Text;

// Prints every System.Reflection.Emit.OpCode, sorted by opcode value, one tab-separated line each:
// name size byte1 byte2 operand-type flow-control stack-pop stack-push opcode-type
// byte2 is "-" for one-byte opcodes. With an output path argument the lines are written to that
// file as UTF-8 without BOM; otherwise they go to stdout.
internal static class Program
{
    private static int Main(string[] args)
    {
        if (args.Length > 1)
        {
            Console.Error.WriteLine("usage: opcodes-dump [output-file]");
            return 2;
        }

        var opcodes = typeof(OpCodes)
            .GetFields(BindingFlags.Public | BindingFlags.Static)
            .Where(f => f.FieldType == typeof(OpCode))
            .Select(f => (OpCode)f.GetValue(null))
            .OrderBy(op => (ushort)op.Value)
            .ToList();

        var sb = new StringBuilder();
        foreach (var op in opcodes)
        {
            int value = (ushort)op.Value;
            int size = op.Size;
            string byte1 = (size == 1 ? value : value >> 8).ToString("X2");
            string byte2 = size == 1 ? "-" : (value & 0xFF).ToString("X2");
            sb.Append(string.Join("\t",
                op.Name, size, byte1, byte2,
                op.OperandType, op.FlowControl, op.StackBehaviourPop, op.StackBehaviourPush, op.OpCodeType))
              .Append('\n');
        }

        if (args.Length == 1)
        {
            File.WriteAllText(args[0], sb.ToString(), new UTF8Encoding(false));
        }
        else
        {
            Console.Out.Write(sb.ToString());
        }

        return 0;
    }
}
