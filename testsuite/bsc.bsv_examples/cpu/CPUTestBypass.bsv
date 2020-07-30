/*----------------------------------------------------------------------------

CPUTestBypass

This is a testbench for FiveStageCPUBypass.
 
The testbench executes a simple program which should have the following
trace through the pipeline:
 
(In this picture, the items under Fetch are the items which will
be next loaded from memory.  The items under decode indicate
the item waiting in the BF buffer.  The items under the other
stages indicate the items waiting in the buffers before those
stages.  Thus, for any item, there needs to be one cycle of no
stall before the item moves to the next column.  The first Add
instruction stalls twice, thus it is at the head of the BF buffer
for three cycles.)

Time   Fetch      Decode    Execute     Memory   Writeback
----+----------+----------+----------+----------+----------+
  0 | LoadC R0 |          |          |          |          |
    |          |          |          |          |          |
----+----------+----------+----------+----------+----------+
  1 | LoadC R1 | LoadC R0 |          |          |          |
    |          |          |          |          |          |
----+----------+----------+----------+----------+----------+
  2 | LoadC R2 | LoadC R1 | LoadC R0 |          |          |
    |          |          |          |          |          |
----+----------+----------+----------+----------+----------+
  3 | Add R3   | LoadC R2 | LoadC R1 | LoadC R0 |          |
    |   R0 R1  |          |          |          |          |
----+----------+----------+----------+----------+----------+ 
  4 | Add R4   | Add R3   | LoadC R2 | LoadC R1 | LoadC R0 | Bypass: R0 and R1
    |   R3 R2  |   R0 R1  |          |          |          |  available **
----+----------+----------+----------+----------+----------+
  5 | Store    | Add R4   | Add R3   | LoadC R2 | LoadC R1 | Stall: R3 not
    |   R4 R1  |   R3 R2  |   R0 R1  |          |          |  loaded yet
----+----------+----------+----------+----------+----------+
  6 | Store    | Add R4   |          | Add R3   | LoadC R2 | Bypass: R3 and R2
    |   R4 R1  |   R3 R2  |          |   R0 R1  |          |  available
----+----------+----------+----------+----------+----------+
  7 | LoadC R5 | Store    | Add R4   |          | Add R3   | Stall: R4 not
    |          |   R4 R1  |   R3 R2  |          |   R0 R1  |  loaded yet
----+----------+----------+----------+----------+----------+
  8 | LoadC R5 | Store    |          | Add R4   |          | Bypass: R4
    |          |   R4 R1  |          |   R3 R2  |          |  available
----+----------+----------+----------+----------+----------+
  9 | Jz R0 R5 | LoadC R5 | Store    |          | Add R4   |
    |          |          |   R4 R1  |          |   R3 R2  |
----+----------+----------+----------+----------+----------+
 10 | Add R4   | Jz R0 R5 | LoadC R5 | Store    |          | Stall: R5 not
    |   R4 R4  |          |          |   R4 R1  |          |  available ***
----+----------+----------+----------+----------+----------+
 11 | Add R4   | Jz R0 R5 |          | LoadC R5 | Store    | Bypass: R5
    |   R4 R4  |          |          |          |   R4 R1  |  available
----+----------+----------+----------+----------+----------+
 12 | Store    | Add R4   | Jz R0 R5 |          | LoadC R5 | Jump clears PC
    |   R4 R0  |   R4 R4  |          |          |          | (decode stalls,
----+----------+----------+----------+----------+----------+  and no fetch)
 13 | Store    |          |          |          |          |
    |   R4 R0  |          |          |          |          |
----+----------+----------+----------+----------+----------+
 14 | Halt     | Store    |          |          |          |
    |          |   R4 R0  |          |          |          |
----+----------+----------+----------+----------+----------+
 15 |          | Halt     | Store    |          |          |
    |          |          |   R4 R0  |          |          |
----+----------+----------+----------+----------+----------+
 16 |          | Halt     |          | Store    |          |
    |          |          |          |   R4 R0  |          |
----+----------+----------+----------+----------+----------+

** If bypassing is improperly implemented, this instruction could get
the wrong value for R0.  Remember that writes to R0 are ignored, so
bypassing should ignore R0.

*** In this CPU, we have chosen not to bypass from the buffer after
the decode stage.  However, the LoadC instruction could be bypassed
from that point (no computation is needed to determine the value to
be loaded).  We have no chosen to implement this, so a stall occurs
at the indicated point.

And as observed, there are 17 cycles in the operation of the CPU.
The total simulation time is 11 cycles of writing to the instruction
memory, 1 cycle to start the CPU, and 17 cycles of operation = 29.
As expected, the simulation runs from 0 to 290 (cycle time is 10).

-----------------------------------------------------------------------------*/

import FiveStageCPUBypass::*;

typedef Bit#(32) MemAddr;

typedef union tagged {
    MemAddr WriteIMem;
    MemAddr WriteDMem;
    void Start;
    void Running;
} TestStage deriving (Eq, Bits);

module mkCPUTestBypass(Empty);
  CPU cpu();
  mkFiveStageCPUBypass the_cpu(cpu);

  Reg#(TestStage) state();
  mkReg#(WriteIMem(0)) the_state(state);

  MemAddr maxInstr = 10;
  function Instr nextInstr(MemAddr n);
   case (n)
      0 :  return (LoadC {rd:R0, v:10});
      1 :  return (LoadC {rd:R1, v:15});
      2 :  return (LoadC {rd:R2, v:20}); 
      3 :  return (Add {rd:R3, ra:R0, rb:R1});
      4 :  return (Add {rd:R4, ra:R3, rb:R2});
      5 :  return (Store {v:R4, addr:R1});
      6 :  return (LoadC {rd:R5, v: 9});
      7 :  return (Jz {cd:R0, addr:R5});
      8 :  return (Add {rd:R4, ra:R4, rb:R4});
      9 :  return (Store {v:R4, addr:R0});
     10 :  return (Halt);
   endcase

// Program involving potential new instruction:
//   case (n)
//     0 :  return (LoadC {rd:R0, v:10});
//     1 :  return (LoadC {rd:R1, v:15});
//     2 :  return (LoadPC {rd:R3});
//     3 :  return (LShift {rd:R5, ra:R3, rb:R3});
//     4 :  return (Store {v:R5, addr:R6});
//     5 :  return (Add {rd:R2, ra:R0, rb:R1});
//     6 :  return (Store {v:R2, addr:R3});
//   endcase
  endfunction: nextInstr

  rule writing_InstrMem (state matches (tagged WriteIMem .n));
     cpu.imem.put(n, zeroExtend(pack(nextInstr(n))));
     state <= (n == maxInstr ? Start : WriteIMem (n + 1));
  endrule: writing_InstrMem

  rule starting_CPU (state matches Start);
     cpu.start;
     state <= Running;
  endrule: starting_CPU

  rule done (state matches Running &&& cpu.done);
     $display("DMem location %d has value %d at time %d",
	      0, cpu.dmem.get(0), $stime);
     $finish(0);
  endrule: done

endmodule: mkCPUTestBypass

