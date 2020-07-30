import ValueImports::*;
//import ActionImports::*;
import ActionValueImports::*;

(* synthesize *)
module mkTestMultipleRules ();
   Reg#(Bit#(32)) state <- mkReg(0);

   // test input from register
   Reg#(Bit#(32)) n <- mkReg(64);

   // static inputs
   Bit#(128) w = const_wide;
   Bit#(64) p = {const_narrow, const_narrow};
   String s = "Hi mom!";

   // test write to register
   Reg#(Bit#(32))  res_n <- mkReg(0);
   Reg#(Bit#(128)) res_w <- mkReg(0);
   Reg#(Bit#(64))  res_p <- mkReg(0);

   // test value functions in conditions, and shared among rules (CSE)
   rule r1 ((state == 0) && (const_narrow == 17));
      $display("Rule r1");
      $display(" and32 = %h", and32('1,const_narrow));
      $display(" and128 = %h", and128('1,const_wide));
      $display(" andN = %h", andN('1,p));
      state <= state + 1;
   endrule

   rule r2 ((state == 1) && (const_narrow == 17));
      $display("Rule r2");
      $display(" and32 = %h", and32('1,const_narrow));
      $display(" and128 = %h", and128('1,const_wide));
      $display(" andN = %h", andN('1,p));
      state <= state + 1;
   endrule

   // test conditional actions
   rule r3 ((state == 2) && (const_wide == const_wide));
      $display("Rule r3");

      Bit#(32) rn1 <- av_narrow (w, p, n, s);
      $display(" rn1 = %h", rn1);
      if (rn1 == 8) /* True */
	 $display(" and32 1 = %h", and32('1,const_narrow));
      if (rn1 != 8) /* False */
	 $display(" and32 2 = %h", and32('0,const_narrow));
      res_n <= rn1;

      Bit#(128) rw1 <- av_wide (s, n, p, w);
      $display(" rw1 = %h", rw1);
      if (rw1 != ~w) /* False */
	 $display(" and128 1 = %h", and128('1,const_wide));
      if (rw1 == ~w) /* True */
	 $display(" and128 2 = %h", and128(17,const_wide));
      res_w <= rw1;

      Bit#(64) rp1 <- av_poly (p, s, w, n);
      $display(" rp1 = %h", rp1);
      if (rp1 == ~p) /* True */
	 $display(" andN 1 = %h", andN('1,p));
      if (rp1 != ~p) /* False */
	 $display(" andN 2 = %h", andN(17,p));
      res_p <= rp1;

      state <= state + 1;
   endrule

   // test shared actionvalues
   rule r4 (state == 3);
      $display("Rule r4");

      Bit#(32) rn1 <- av_narrow (w, p, n, s);
      $display(" rn1 = %h", rn1);
      // might as well test the same value calls too
      $display(" and32 1 = %h", and32('1,const_narrow));
      $display(" and32 2 = %h", and32('0,const_narrow));

      Bit#(128) rw1 <- av_wide (s, n, p, w);
      $display(" rw1 = %h", rw1);
      $display(" and128 1 = %h", and128('1,const_wide));
      $display(" and128 2 = %h", and128(17,const_wide));

      Bit#(64) rp1 <- av_poly (p, s, w, n);
      $display(" rp1 = %h", rp1);
      $display(" andN 1 = %h", andN('1,p));
      $display(" andN 2 = %h", andN(17,p));

      state <= state + 1;
   endrule

   rule display_state (state == 4);
      $display(" res_n = %h", res_n);
      $display(" res_w = %h", res_w);
      $display(" res_p = %h", res_p);
      state <= state + 1;
   endrule

   rule done (state == 5);
      $finish(0);
   endrule

   Reg#(UInt#(7)) watchdog <- mkReg(0);
   
   rule check_watchdog;
     if(watchdog > 100) begin
        $display("Watchdog check failed\n");
        $finish(0);
     end
     watchdog <= watchdog + 1;
   endrule

endmodule

