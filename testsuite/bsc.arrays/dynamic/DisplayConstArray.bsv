import Vector::*;

(* synthesize *)
module sysDisplayConstArray();
   Reg#(Bit#(2)) idx <- mkReg(0);

   rule do_disp;
      Vector#(4, Bit#(8)) vec;
      vec[0] = 17;
      vec[1] = 2;
      vec[2] = 42;
      vec[3] = 22;
      $display(vec[idx]);
   endrule
endmodule
