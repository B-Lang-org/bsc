// In this example, AOpt performs boolean optimization, because
// all the pieces are in the ASPackage defs.

// By putting half the logic on the input to an RWire and half on
// the output, we can guarantee that the logic will only be available
// for optimization in the Verilog backend, when the RWire is inlined.

// The "|| x" applied to the output of the RWire can be optimized away.
// The generated Verilog for this example has just "x" and not "x || x".

(* synthesize *)
module sysOptAcrossRWireInDefs (Empty);
   Reg#(Bool) x <- mkRegU;
   Reg#(Bool) y <- mkRegU;
   
   RWire#(Bool) rw <- mkRWire;

   rule rule1;
      rw.wset(x);
   endrule

   rule rule2 (isValid(rw.wget));
      x <= validValue(rw.wget) || x;
   endrule
endmodule

