//Parser bug prevents this code from working
//Bool x[2] = {True, True};
//Bit#(1) y = x[0];

import Vector::*;

module test();
   
   Bit#(1) y = 1;   
   Reg#(Vector#(2,Bool)) v <- mkReg(replicate(False));
   
   rule t;
      v[0] <= y;
   endrule
   
endmodule
