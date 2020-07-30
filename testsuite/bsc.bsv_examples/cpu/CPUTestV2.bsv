/*----------------------------------------------------------------------------

CPUTestV2

This is a testbench for FiveStageCPUStallV2.

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
----+----------+----------+----------+----------+----------+ Stall: R0 and R1
  4 | Add R4   | Add R3   | LoadC R2 | LoadC R1 | LoadC R0 |  needed by Add
    |   R3 R2  |   R0 R1  |          |          |          |  not loaded yet
----+----------+----------+----------+----------+----------+
  5 | Add R4   | Add R3   |          | LoadC R2 | LoadC R1 | Stall: R0 and R1
    |   R3 R2  |   R0 R1  |          |          |          |  not loaded yet
----+----------+----------+----------+----------+----------+
  6 | Add R4   | Add R3   |          |          | LoadC R2 |
    |   R3 R2  |   R0 R1  |          |          |          |
----+----------+----------+----------+----------+----------+
  7 | Store    | Add R4   | Add R3   |          |          | Stall: R3 and R2
    |   R4 R1  |   R3 R2  |   R0 R1  |          |          |  not loaded yet
----+----------+----------+----------+----------+----------+
  8 | Store    | Add R4   |          | Add R3   |          | Stall: R3 not
    |   R4 R1  |   R3 R2  |          |   R0 R1  |          |  loaded yet
----+----------+----------+----------+----------+----------+
  9 | Store    | Add R4   |          |          | Add R3   | Stall: R3 not 
    |   R4 R1  |   R3 R2  |          |          |   R0 R1  |  loaded yet
----+----------+----------+----------+----------+----------+
 10 | Store    | Add R4   |          |          |          |
    |   R4 R1  |   R3 R2  |          |          |          |
----+----------+----------+----------+----------+----------+
 11 | LoadC R5 | Store    | Add R4   |          |          | Stall: R4 not 
    |          |   R4 R1  |   R3 R2  |          |          |  loaded yet
----+----------+----------+----------+----------+----------+
 12 | LoadC R5 | Store    |          | Add R4   |          | Stall: R4 not 
    |          |   R4 R1  |          |   R3 R2  |          |  loaded yet
----+----------+----------+----------+----------+----------+
 13 | LoadC R5 | Store    |          |          | Add R4   | Stall: R4 not 
    |          |   R4 R1  |          |          |   R3 R2  |  loaded yet
----+----------+----------+----------+----------+----------+
 14 | LoadC R5 | Store    |          |          |          |
    |          |   R4 R1  |          |          |          |
----+----------+----------+----------+----------+----------+
 15 | Jz R0 R5 | LoadC R5 | Store    |          |          | 
    |          |          |   R4 R1  |          |          | 
----+----------+----------+----------+----------+----------+
 16 | Add R4   | Jz R0 R5 | LoadC R5 | Store    |          | Stall: R5 not
    |   R4 R4  |          |          |   R4 R1  |          |  loaded yet
----+----------+----------+----------+----------+----------+
 17 | Add R4   | Jz R0 R5 |          | LoadC R5 |          | Stall: R5 not
    |   R4 R4  |          |          |          |          |  loaded yet
----+----------+----------+----------+----------+----------+
 18 | Add R4   | Jz R0 R5 |          |          | LoadC R5 | Stall: R5 not
    |   R4 R4  |          |          |          |          |  loaded yet
----+----------+----------+----------+----------+----------+
 19 | Add R4   | Jz R0 R5 |          |          |          |
    |   R4 R4  |          |          |          |          |
----+----------+----------+----------+----------+----------+
 20 | Store    | Add R4   | Jz R0 R5 |          |          | Jump clears PC,
    |   R4 R0  |   R4 R4  |          |          |          | (decode stalls,
----+----------+----------+----------+----------+----------+  and no fetch)
 21 | Store    |          |          |          |          | 
    |   R4 R0  |          |          |          |          |
----+----------+----------+----------+----------+----------+
 22 | Halt     | Store    |          |          |          |
    |          |   R4 R0  |          |          |          |
----+----------+----------+----------+----------+----------+
 23 |          | Halt     | Store    |          |          |
    |          |          |   R4 R0  |          |          |
----+----------+----------+----------+----------+----------+
 24 |          | Halt     |          | Store    |          |
    |          |          |          |   R4 R0  |          |
----+----------+----------+----------+----------+----------+

And as observed, there are 25 cycles in the operation of the CPU.
The total simulation time is 11 cycles of writing to the instruction
memory, 1 cycle to start the CPU, and 25 cycles of operation = 37.
As expected, the simulation runs from 0 to 370 (cycle time is 10).

-----------------------------------------------------------------------------*/

import FiveStageCPUStallV2::*;

typedef Bit#(32) MemAddr;

typedef union tagged {
    MemAddr WriteIMem;
    MemAddr WriteDMem;
    void Start;
    void Running;
} TestStage deriving (Eq, Bits);

module mkCPUTestV2(Empty);
  CPU cpu();
  mkFiveStageCPUStall the_cpu(cpu);

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

endmodule: mkCPUTestV2

