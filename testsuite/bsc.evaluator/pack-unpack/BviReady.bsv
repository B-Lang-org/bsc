package BviReady;

// import-BVI ready signals are desugared through unpack (CQFilter);
// with a constant-1 RDY the method must still be provably always ready
// (the constant must fold through the coercion).
import "BVI" ConstRdy =
   module mkConstRdy(ConstRdyIfc);
      default_clock clk(CLK);
      default_reset no_reset;
      method OUT out() ready(RDY);
      schedule out CF out;
   endmodule

interface ConstRdyIfc;
   method Bit#(8) out();
endinterface

(* synthesize *)
module mkBviReady();
   ConstRdyIfc dut <- mkConstRdy;
   Reg#(Bit#(8)) r <- mkRegU;
   rule grab;
      r <= dut.out();
   endrule
endmodule

endpackage
