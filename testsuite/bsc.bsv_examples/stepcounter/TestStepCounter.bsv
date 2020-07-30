package TestStepCounter;

import StepCounter::*;

// testbench for step counter
(* synthesize *)
module sysTestStepCounter(Empty);

  // make a test counter of Bit#(23) starting at 4 with step 3
  StepCounter#(Bit#(23)) test_counter();
  mkStepCounter#(4,3) i_test_counter(test_counter);

  // count cycles for testbench
  Reg#(Bit#(4)) cycles();
  mkReg#(0) i_cycles(cycles);

  // run for 10 cycles
  rule run (True);
    if (cycles < 10)
      cycles <= cycles + 1;
    else
      $finish(0);
  endrule

  rule test (True); 
     $display("Cycle: %0d Value: %0d", cycles, test_counter.value);
  endrule

  // triggers counting at certain cycles
  rule count (True);
    case (cycles) 
      0,2,3,5,7: test_counter.count();
      default: noAction;
    endcase
  endrule

endmodule

// alternative: separately synthesizing the step counter 
// The always_ready attribute is used to drop the ready signals
// since they are always True anyway
(* synthesize, always_ready *)
module sysStepCounter17(StepCounter#(Int#(17)));
  StepCounter#(Int#(17)) my_counter();
  mkStepCounter#(-1987,23) i_my_counter(my_counter);
  return(my_counter);
endmodule

endpackage
