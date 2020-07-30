// In this example, AOpt does not perform boolean optimization,
// because the expression is in the foreign blocks of the ASPackage
// (where optimization is not currently applied).

// By putting half the logic on the input to an RWire and half on
// the output, we can guarantee that the logic will only be available
// for optimization in the Verilog backend, when the RWire is inlined.

// The "|| x" applied to the output of the RWire can be optimized away.
// The generated Verilog for this example, however, contains "x || x".

(* synthesize *)
module sysOptAcrossRWireInForeign (Empty);
   Reg#(Bool) x <- mkRegU;
   Reg#(Bool) y <- mkRegU;
   
   RWire#(Bool) rw <- mkRWire;

   rule rule1;
      rw.wset(x);
   endrule

   rule rule2 (isValid(rw.wget));
      $display(validValue(rw.wget) || x);
   endrule
endmodule


