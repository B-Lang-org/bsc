(* synthesize *)
module sysTestPlusargsSimple ();

   Reg#(Bool) b <- mkReg(True);

   rule disp_rule (b);
      Bool v <- $test$plusargs("He");
      $display("v = %h", v);
      b <= False;
   endrule

   rule end_rule (!b);
      $finish(0);
   endrule

endmodule
