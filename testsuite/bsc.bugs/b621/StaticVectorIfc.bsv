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
module sysStaticVectorIfc ();

  Reg#(Bit#(16)) n <- mkReg(0);
  Reg#(UInt#(5)) numTests <- mkReg(1);
  
  Vectored dut <- mkVectored();
  
  rule test0 (n == 0);
  
    dut.my_vec[0].amethod(0);

    $display("%0d", dut.my_vec[0].vmethod());

  endrule

  rule test1 (n == 1);
  
    dut.my_vec[1].amethod(1);

    $display("%0d", dut.my_vec[1].vmethod());

  endrule
  
  rule test2 (n == 2);
  
    dut.my_vec[2].amethod(2);

    $display("%0d", dut.my_vec[2].vmethod());

  endrule

  rule incr (True);
  
    if (n == 2) n <= 0; else n <= n + 1;

    numTests <= numTests + 1;
    
  endrule

  rule endtests (numTests == 31);
  
    $finish(0);
  
  endrule

endmodule
