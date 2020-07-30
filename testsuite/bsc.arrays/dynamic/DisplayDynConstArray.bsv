(* synthesize *)
module sysDisplayDynConstArray();
   Reg#(Bool) c <- mkReg(True);
   Reg#(Bit#(2)) idx <- mkReg(0);

   rule do_disp;
      Bit#(8) v1[4] = { 1, 2, 3, 4 };
      Bit#(8) v2[4] = { 4, 3, 2, 1 };

      let vec = (c ? v1 : v2);

      $display(vec[idx]);
   endrule
endmodule
