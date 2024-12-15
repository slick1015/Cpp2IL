using System;
using System.Linq;
using System.Collections.Generic;
using LibCpp2IL;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Graphs.Analysis.Stack;

/* The whole purpose of this class is to try analyze the stack state of a method.
 * With this information we should be able to determine the offset of the stack 
 * for instructions and blocks and correct "move stack(0xXX) , reg10" instructions
 * without a correct stack offset. Also NOP shift stack instructions.
 */
public sealed class StackAnalyzer
{
    private HashSet<Block<InstructionSetIndependentInstruction>> visited = [];

    // Stack offset for each block we have. To my knowledge this should be consistent.
    // If it's not then its a problem (should be a very small % of cases)
    // Most of these mismatches currently are because of switch/exception catchers
    // which are not implemented yet.
    private Dictionary<Block<InstructionSetIndependentInstruction>, StackEntry> inComingDelta = [];
    private Dictionary<Block<InstructionSetIndependentInstruction>, StackEntry> outGoingDelta = [];

    private Dictionary<InstructionSetIndependentInstruction, StackEntry> instructionsStackState = [];

    // debug
    public static int unbalancedStackCount { get; private set; } = 0;
    public static int balanacedStackCount { get; private set; } = 0;

    private StackAnalyzer() { }

    public static bool Analyze(MethodAnalysisContext context)
    {
        try
        {
            var graph = context.ControlFlowGraph;
            if (graph == null)
            {
                return false;
            }
            var analyzer = new StackAnalyzer();
            analyzer.inComingDelta[graph.EntryBlock] = new StackEntry();
            var archSize = LibCpp2IlMain.Binary!.is32Bit ? 4 : 8;
            analyzer.TraverseGraph(graph.EntryBlock, archSize);
            var outDelta = analyzer.outGoingDelta[graph.ExitBlock];
            if (outDelta.StackState.Count != 0)
            {
                // This method ends with a non-empty stack, let's just bail early for now
                unbalancedStackCount++;
                return false;
            }
            else
            {
                foreach(var block in graph.Blocks)
                {
                    InstructionSetIndependentInstruction? previousInstruction = null;
                    foreach (var instruction in block.Instructions)
                    {
                        var currentPos = (analyzer.instructionsStackState[instruction].StackState.Count) * archSize;

                        /*
                         *   Push/Pop
                         *       builder.ShiftStack(instruction.IP, -operandSize);
                         *       builder.Move(instruction.IP, InstructionSetIndependentOperand.MakeStack(0), ConvertOperand(instruction, 0));
                         */
                        if (instruction.OpCode.Mnemonic == IsilMnemonic.ShiftStack)
                        {
                            // NOP the shift stack instruction
                            instruction.OpCode = InstructionSetIndependentOpCode.Nop;
                            instruction.Operands = [];
                            // Correct stack offset for previous move instruction if it matches (push/pop combo)
                            if (previousInstruction != null &&
                                previousInstruction.OpCode == InstructionSetIndependentOpCode.Move &&
                                previousInstruction.Operands is [InstructionSetIndependentOperand { Type: InstructionSetIndependentOperand.OperandType.StackOffset, Data: IsilStackOperand { Offset: 0 } }, InstructionSetIndependentOperand op2]) 
                            { 
                                previousInstruction.Operands = [InstructionSetIndependentOperand.MakeStack(currentPos), op2];
                            }
                        }
                        previousInstruction = instruction;
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
                return true;

            }
        }
        catch (Exception e)
        {
            unbalancedStackCount++;
            return false;
        }
    }



    // Traverse the graph and calculate the stack state for each block and instruction
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
