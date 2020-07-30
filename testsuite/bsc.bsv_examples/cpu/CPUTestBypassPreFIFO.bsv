/*----------------------------------------------------------------------------

CPUTestBypassPreFIFO

This is a testbench for FiveStageCPUBypassPreFIFO.
 
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
  5 | Store    | Add R4   | Add R3   | LoadC R2 | LoadC R1 | Bypass: R3 and R2
    |   R4 R1  |   R3 R2  |   R0 R1  |          |          |  available *
----+----------+----------+----------+----------+----------+
  6 | LoadC R5 | Store    | Add R4   | Add R3   | LoadC R2 | Bypass: R1 and R4
    |          |   R4 R1  |   R3 R2  |   R0 R1  |          |  available *
----+----------+----------+----------+----------+----------+
  7 | Jz R0 R5 | LoadC R5 | Store    | Add R4   | Add R3   |
    |          |          |   R4 R1  |   R3 R2  |   R0 R1  |
----+----------+----------+----------+----------+----------+
  8 | Add R4   | Jz R0 R5 | LoadC R5 | Store    | Add R4   | Bypass: R5
    |   R4 R4  |          |          |   R4 R1  |   R3 R2  |  available ***
----+----------+----------+----------+----------+----------+
  9 | Store    | Add R4   | Jz R0 R5 | LoadC R5 | Store    | Jump clears PC
    |   R4 R0  |   R4 R4  |          |          |   R4 R1  | (decode stalls,
----+----------+----------+----------+----------+----------+  and no fetch)
 10 | Store    |          |          |          | LoadC R5 |
    |   R4 R0  |          |          |          |          |
----+----------+----------+----------+----------+----------+
 11 | Halt     | Store    |          |          |          |
    |          |   R4 R0  |          |          |          |
----+----------+----------+----------+----------+----------+
 12 |          | Halt     | Store    |          |          |
    |          |          |   R4 R0  |          |          |
----+----------+----------+----------+----------+----------+
 13 |          | Halt     |          | Store    |          |
    |          |          |          |   R4 R0  |          |
----+----------+----------+----------+----------+----------+

* Here is an instance of bypassing immediately from the computation
in the execute stage, before the value gets registered in the BE FIFO.

** If bypassing is improperly implemented, this instruction could get
the wrong value for R0.  Remember that writes to R0 are ignored, so
bypassing should ignore R0.

*** In this CPU, we have chosen not to bypass from the buffer after
the decode stage.  However, the LoadC instruction could be bypassed
from that point (no computation is needed to determine the value to
be loaded).  We have no chosen to implement this, so in the first
bypass version of the CPU, a stall occurs at the indicated point.
In this version, there is no stall, because we bypass immediately
from the execution stage.  So we get the LoadC bypass without needing
to bypass from the decode buffer.

And as observed, there are 14 cycles in the operation of the CPU.
The total simulation time is 11 cycles of writing to the instruction
memory, 1 cycle to start the CPU, and 14 cycles of operation = 26.
As expected, the simulation runs from 0 to 260 (cycle time is 10).

-----------------------------------------------------------------------------*/

import FiveStageCPUBypassPreFIFO::*;

typedef Bit#(32) MemAddr;

typedef union tagged {
    MemAddr WriteIMem;
    MemAddr WriteDMem;
    void Start;
    void Running;
} TestStage deriving (Eq, Bits);

module mkCPUTestBypassPreFIFO(Empty);
  CPU cpu();
  mkFiveStageCPUBypassPreFIFO the_cpu(cpu);

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

endmodule: mkCPUTestBypassPreFIFO

