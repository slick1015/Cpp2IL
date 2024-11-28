using System;
using System.Collections.Generic;
using LibCpp2IL;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using System.Linq;

namespace Cpp2IL.Core.Graphs.Analysis.Stack;

public sealed class StackAnalyzer
{
    private HashSet<Block<InstructionSetIndependentInstruction>> visited = [];

    // This is overkill and slow but it works for now
    private Dictionary<Block<InstructionSetIndependentInstruction>, StackEntry> inComingDelta = [];
    private Dictionary<Block<InstructionSetIndependentInstruction>, StackEntry> outGoingDelta = [];

    private Dictionary<InstructionSetIndependentInstruction, StackEntry> instructionsStackState = [];

    // debug
    public static int unbalancedStackCount { get; private set; } = 0;
    public static int balanacedStackCount { get; private set; } = 0;

    private StackAnalyzer() { }

    public static void Analyze(MethodAnalysisContext context)
    {
        try
        {
            var graph = context.ControlFlowGraph;
            if (graph == null)
            {
                return;
            }
            var analyzer = new StackAnalyzer();
            analyzer.inComingDelta[graph.EntryBlock] = new StackEntry();
            var archSize = LibCpp2IlMain.Binary!.is32Bit ? 4 : 8;
            analyzer.TraverseGraph(graph.EntryBlock, archSize);
            var outDelta = analyzer.outGoingDelta[graph.ExitBlock];
            if (outDelta.StackState.Count != 0)
            {
                unbalancedStackCount++;
            }
            else
            {
                
                foreach(var block in graph.Blocks)
                {
                    foreach (var instruction in block.Instructions)
                    {
                        var currentPos = (analyzer.instructionsStackState[instruction].StackState.Count) * archSize;
                        if (instruction.OpCode.Mnemonic == IsilMnemonic.Push)
                        {
                            instruction.OpCode = InstructionSetIndependentOpCode.Move;
                            instruction.Operands = [InstructionSetIndependentOperand.MakeStack(currentPos), instruction.Operands[1]];
                        }
                        else if (instruction.OpCode.Mnemonic == IsilMnemonic.Pop)
                        {

                            instruction.OpCode = InstructionSetIndependentOpCode.Move;
                            instruction.Operands = [instruction.Operands[0], InstructionSetIndependentOperand.MakeStack(currentPos)];
                        }
                        else if (instruction.OpCode.Mnemonic == IsilMnemonic.ShiftStack)
                        {
                            instruction.OpCode = InstructionSetIndependentOpCode.Nop;
                            instruction.Operands = [];
                        } 
                    }
                    if (block.BlockType == BlockType.Call)
                    {
                        var callInstruction = block.Instructions[^1];
                        
                        var stackState = analyzer.instructionsStackState[callInstruction].StackState;
                        var stackSize = stackState.Count * archSize;
                        for (int i = 0; i < callInstruction.Operands.Length; i++)
                        {
                            var op = callInstruction.Operands[i];
                            if (op.Type == InstructionSetIndependentOperand.OperandType.StackOffset)
                            {
                                
                                var actual = stackSize - ((IsilStackOperand)op.Data).Offset;
                                callInstruction.Operands[i] = InstructionSetIndependentOperand.MakeStack(actual);
                            }
                        }

                        // Filter out stack operands with an offset < 0, we've overestimated how many actual args this function has
                        callInstruction.Operands = callInstruction.Operands.Where(op => op.Type != InstructionSetIndependentOperand.OperandType.StackOffset || ((IsilStackOperand)op.Data).Offset > stackSize).ToArray();
                    }
                }
                balanacedStackCount++;

            }
        }
        catch (Exception e)
        {
            unbalancedStackCount++;
        }
    }

    private void TraverseGraph(Block<InstructionSetIndependentInstruction> block, int archSize)
    {
        var blockDelta = inComingDelta[block].Clone();

        // TODO: Handle interrupt blocks: Call -> Interrupt -> Exit
        if (block.BlockType == BlockType.Call && block.Successors.Count == 1 && block.Successors[0].BlockType == BlockType.Exit)
        {
            // still need to calculate it for instructions
            // Tail call / CallNoReturn = Flush stack?
            blockDelta.StackState.Clear();
            outGoingDelta[block] = blockDelta;
        }
        else
        {
            var previous = blockDelta;
            foreach (var instruction in block.Instructions)
            {
                instructionsStackState[instruction] = previous;

                switch (instruction.OpCode.Mnemonic)
                {
                    case IsilMnemonic.Push:
                        previous = previous.Clone();
                        previous.PushEntry("push");
                        break;
                    case IsilMnemonic.Pop:
                        previous = previous.Clone();
                        previous.PopEntry();
                        break;
                    case IsilMnemonic.ShiftStack:
                        var value = (int)((IsilImmediateOperand)instruction.Operands[0].Data).Value;
                        if (value % archSize != 0)
                        {
                            throw new Exception("Unaligned stack shift");
                        } else
                        {
                            previous = previous.Clone();
                            for (int i = 0; i < Math.Abs(value / archSize); i++)
                            {
                                if (value < 0)
                                {
                                    previous.PushEntry("allocated space");
                                }
                                else
                                {
                                    previous.PopEntry();
                                }
                            }
                        }
                        break;
                }
            }
            blockDelta = previous;
            outGoingDelta[block] = blockDelta;
        }

        foreach (var succ in block.Successors)
        {
            if (!visited.Contains(succ))
            {
                inComingDelta[succ] = blockDelta;
                visited.Add(succ);
                TraverseGraph(succ, archSize);
            }
            else
            {
                var expectedDelta = inComingDelta[succ];

                if (expectedDelta.StackState.Count != blockDelta.StackState.Count)
                {
                    // TODO: Investigate SystemGuid::.ctor(Byte[]), stack appears to be well formed but results in unbalanced stack somehow
                    // TODO: Investigate System.WeakReference::get_Target(), has some wack stack manipulation
                    throw new Exception("Unbalanced stack");
                }
                inComingDelta[succ] = blockDelta;
            }
        }
    }
}
