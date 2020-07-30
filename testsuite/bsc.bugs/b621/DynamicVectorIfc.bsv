import Vector::*;

interface Simple;
  method Bit#(16) vmethod();
  method Action   amethod(Bit#(16) x);
endinterface

interface Vectored;
  interface Vector#(3, Simple) my_vec;
endinterface

module mkSimple#(Reg#(Bit#(16)) r) (Simple);
  
  method vmethod = r;
  method Action amethod(Bit#(16) x);
    r <= x;
  endmethod

endmodule

(* synthesize *)
module mkVectored (Vectored);

  Reg#(Bit#(16)) r <- mkReg(1000);
  
  
  Vector#(3, Simple) v = replicate(?);
  
  for (Integer x = 0; x < 3; x = x + 1)
    v[x] <- mkSimple(r);
  
  interface my_vec = v;
  
endmodule


(* synthesize *)
module sysDynamicVectorIfc ();

  Reg#(Bit#(16)) n <- mkReg(0);
  Reg#(UInt#(5)) numTests <- mkReg(1);
  
  Vectored dut <- mkVectored();
  
  rule test (True);
  
    select(dut.my_vec, n).amethod(n);

    $display("%0d", select(dut.my_vec, n).vmethod());
    
    if (n == 2) n <= 0; else n <= n + 1;

    numTests <= numTests + 1;

  endrule

  rule endtests (numTests == 31);
  
    $finish(0);
  
  endrule

endmodule
