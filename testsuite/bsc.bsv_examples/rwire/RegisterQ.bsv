package RegisterQ;

/*----------------------------------------------------------------------------
Bluespec System Verilog's register primitives (provided by the variants of 
mkReg) describe the simplest kind of primitive state element. It holds a
single value, that can be read and written. From a scheduling perspective, 
reads are constrained to happen before writes (though possibly in parallel) 
so that, even when rules are executied in a single clock cycle, no register 
read observes a stale data value.

There are two straightforward alternatives to the ordinary register:

1. The configuration register (or ConfigReg). This register does not constrain
reads to happen before writes. That means when rules are scheduled in parallel,
stale data values may be observed. This is often used to implement 
configuration registers, where each update clobbers the current value and
the precise order of updates is not important. From a TRS perspective, this 
corresponds to a primitive whose read value is not updated for a finite 
(but undetermined) number of TRS transitions after a write.

2. The bypass register (or BypassReg). This register implements the same 
TRS contract as an ordinary register (i.e. writes take immediate effect), 
but constrains writes to happen *before* reads. Stale data values are never
observed because, in a BypassReg, whenever a value is written it
is also immediately forwarded to the read method of the register. This means
the new value of a BypassReg is available in the same clock cycle as when
it is stored (for reads in rules that execute logically after the writing 
rule, of course), so BypassReg can be a useful primitive for bypassing
values between rules that are expected to execute in parallel.

Both of these primitives can be implemented in pure BSV using only ordinary
registers and RWire, and the exercises below ask you to complete this 
implementations

-----------------------------------------------------------------------------*/

/* For reference, the Reg interface (provided by the Prelude)

 interface Reg #(type a);
     method Action _write(a x1);
     method a _read();
 endinterface: Reg

*/

// mkConfigReg, like mkReg, takes a single parameter to be the initial
// value of the register.
module mkConfigReg#(a v)(Reg#(a)) provisos (Bits#(a,sa));
   
   // an internal register is required
   Reg#(a) cr();
   mkReg#(v) i_cr(cr);
   
   // an internal RWire is also required
   RWire#(a) rw();
   mkRWire i_rw(rw);
 
   // TASK: implement the rest of the ConfigReg interface
   // HINT: an internal rule is also required

   method _read();
     return(?);   
   endmethod

   method _write(a newval);
     action
   
     endaction
   endmethod

endmodule

// Once your implementation of mkConfigReg is complete, you can 
// uncomment this module to synthesize RTL for a ConfigReg.
// Compile and synthesize with the -show-schedule flag to see the method
// scheduling information for the resulting register. Is it correct?
// Compile to Verilog using the -inline-rwire flag and look
// at the resulting RTL. Is it what you expected? 
/*
(* synthesize *)
module sysConfigReg(Reg#(Bit#(16)));
  Reg#(Bit#(16)) r();
  mkConfigReg#(0) the_r(r);
  return (r);
endmodule
*/


// mkBypassReg, like mkReg, takes a single parameter to be the initial
// value of the register.
module mkBypassReg#(a v)(Reg#(a)) provisos (Bits#(a,sa));
 
   // TASK: fill in the implementation of BypassReg
   // HINT: it is very similar to the implementation of ConfigReg

endmodule

// Once your implementation of mkBypassReg is complete, you can 
// uncomment this module to synthesize RTL for a BypassReg
// Compile and synthesize with the -show-schedule flag to see the method
// scheduling information for the resulting register. Is it correct?
// Compile to Verilog using the -inline-rwire flag and look
// at the resulting RTL. Is it what you expected? 
/*
(* synthesize *)
module sysBypassReg(Reg#(Bit#(16)));
  Reg#(Bit#(16)) r();
  mkBypassReg#(0) the_r(r);
  return (r);
endmodule
*/

// Below is an implementation of a self-incrementing 
// 32-bit counter using ordinary registers.
interface Counter32;
  method Bit#(32) count();
endinterface

(* synthesize *)
module mkCounter32(Counter32);
  Reg#(Bit#(32)) count_reg();
  mkReg#(0) i_count_reg(count_reg);
  
  rule step_count (True);
    count_reg <= count_reg + 1;
  endrule

  method count();
    return(count_reg);
  endmethod
endmodule

// TASK: Consider replacing count_reg with a ConfigReg. 
// Does the behavior of the counter change? Why or why not?

// TASK: Consider replacing count_reg with a BypassReg. 
// Does the behaviro of the counter change? Why or why not? 
// HINT: Synthesize Verilog for a counter using BypassReg using
// the -inline-rwire flag

endpackage
