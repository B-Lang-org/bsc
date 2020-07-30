
(* synthesize *)
module sysArrayLength_If();

   Reg#(Bool)   c   <- mkReg(True);

   Bit#(5)      tbl1[3] = { 0, 0, 0 };
   Bit#(5)      tbl2[4] = { 1, 1, 1, 1 };

   rule r;
      let tbl = c ? tbl1 : tbl2;
      $display(arrayLength(tbl));
   endrule
endmodule

