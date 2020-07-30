import Vector::*;

(* synthesize *)
module sysArrayToVector_If();

   Reg#(Vector#(3, Bit#(5)))   rg  <- mkRegU();   

   Reg#(Bool)                  c   <- mkReg(True);

   Bit#(5)                     tbl1[3] = { 0, 0, 0 };
   Bit#(5)                     tbl2[3] = { 1, 1, 1 };

   rule r;
      rg <= arrayToVector(c ? tbl1 : tbl2);
   endrule
endmodule

