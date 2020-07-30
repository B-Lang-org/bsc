(* synthesize *)
module sysStringFormat2 ();
   
   Reg#(Bit#(8))   count     <- mkReg(0);
   Reg#(Bit#(640)) target    <- mkReg(0);
   Reg#(Bit#(640)) targetb   <- mkReg(0);
   Reg#(Bit#(640)) targeto   <- mkReg(0);
   Reg#(Bit#(640)) targeth   <- mkReg(0);
   Reg#(Bit#(640)) targetfmt <- mkReg(0);
   
   rule is_3_mod_4 (count[1:0] == 3);
      $swrite(asIfc(target),   count);
      $swriteb(asIfc(targetb), count);
      $swriteo(asIfc(targeto), count);
      $swriteh(asIfc(targeth), count);
   endrule

   rule is_2_mod_4 (count[1:0] == 2);
      // testing that only 2nd arg is treated as format string
      $sformat(asIfc(targetfmt), "count is %d", count, " with %d", ".");
   endrule
   
   rule is_1_mod_4 (count[1:0] == 1);
      $display("target    = %s", target);
      $display("targetb   = %s", targetb);
      $display("targeto   = %s", targeto);
      $display("targeth   = %s", targeth);
      $display("targetfmt = %s", targetfmt);
   endrule
   
   rule every;
      count <= count + 1;
      if (count == 10) $finish(0);
   endrule

endmodule
