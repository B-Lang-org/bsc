(* synthesize *)
module sysTestPlusargsTwoUseDiffArg ();

   Reg#(Bool) b1 <- mkReg(True);
   Reg#(Bool) b2 <- mkReg(True);

   rule disp_rule_1 (b1);
      Bool v1 <- $test$plusargs("He");
      $display("v1 = %h", v1);
      b1 <= False;
   endrule

   rule disp_rule_2 (!b1 && b2);
      Bool v2 <- $test$plusargs("llo");
      $display("v2 = %h", v2);
      b2 <= False;
   endrule

   rule end_rule (!b1 && !b2);
      $finish(0);
   endrule

endmodule

