
(* synthesize *)
module sysArrayLength_ArrSel();

   Reg#(Bit#(1))   c         <- mkReg(0);

   Bit#(5)         tbl[2][3]  = { { 0, 0, 0 }, { 1, 1, 1 } };

   rule r;
      $display(arrayLength(tbl[c]));
   endrule
endmodule

