(* synthesize *)
module sysStringFormat ();
   
   Reg#(Bit#(8))   count   <- mkReg(0);
   Reg#(Bit#(640)) target  <- mkReg(0);
   Reg#(Bit#(32))  target2 <- mkReg(0);

   rule is_3_mod_4 (count[1:0] == 3);
      $swrite(asIfc(target), "zow %d", count[4:0]);
   endrule

   rule is_2_mod_4 (count[1:0] == 2);
      $swrite(asIfc(target2), "%b", count[3:0]);
   endrule
   
   rule is_1_mod_4 (count[1:0] == 1);
      $display("target  as hex    = %h", target);
      $display("target  as string = %s", target);
      $display("target2 as hex    = %h", target2);
      $display("target2 as string = %s", target2);
   endrule
   
   rule every;
      count <= count + 1;
      if (count == 10) $finish(0);
   endrule

endmodule
