import Vector::*;

(* synthesize *)
module sysArrayToVector_ArrSel();

   Reg#(Vector#(3, Bit#(5)))   rg  <- mkRegU();   

   Reg#(Bit#(3))               idx <- mkReg(0);

   Bit#(5)                     tbl[8][3] = {
      { 0, 0, 0 }, { 0, 0, 1 }, { 0, 1, 0 }, { 0, 1, 1 },
      { 1, 0, 0 }, { 1, 0, 1 }, { 1, 1, 0 }, { 1, 1, 1 }
   };

   rule r;
      rg <= arrayToVector(tbl[idx]);
   endrule
endmodule

