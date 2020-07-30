import ValueImports::*;
import ActionValueImports::*;

import FIFO::*;


(* synthesize *)
module mkTestAggressiveConditions ();
   Reg#(Bit#(32)) state <- mkReg(0);

   // static inputs
   Bit#(32) n = 64;
   Bit#(128) w = const_wide;
   Bit#(64) p = {const_narrow, const_narrow};
   String s = "Hi mom!";

   // FIFOs in order to create implicit conditions
   FIFO#(Bool) f_r1_n1 <- mkFIFO;
   FIFO#(Bool) f_r1_n2 <- mkFIFO;
   FIFO#(Bool) f_r1_w1 <- mkFIFO;
   FIFO#(Bool) f_r1_w2 <- mkFIFO;
   FIFO#(Bool) f_r1_p1 <- mkFIFO;
   FIFO#(Bool) f_r1_p2 <- mkFIFO;

   FIFO#(Bool) f_r2_n1 <- mkFIFO;
   FIFO#(Bool) f_r2_n2 <- mkFIFO;
   FIFO#(Bool) f_r2_w1 <- mkFIFO;
   FIFO#(Bool) f_r2_w2 <- mkFIFO;
   FIFO#(Bool) f_r2_p1 <- mkFIFO;
   FIFO#(Bool) f_r2_p2 <- mkFIFO;

   // test actions conditional on actionvalue function calls
   rule r1 (state == 0);
      $display("Rule r1");

      Bit#(32) rn1 <- av_narrow (w, p, n, s);
      $display(" rn1 = %h", rn1);
      if (rn1 == 8) /* True */ begin
	 f_r1_n1.enq(True);
	 $display(" and32 1 = %h", and32('1,const_narrow));
      end
      if (rn1 != 8) /* False */ begin
	 f_r1_n2.enq(True);
	 $display(" and32 2 = %h", and32('0,const_narrow));
      end

      Bit#(128) rw1 <- av_wide (s, n, p, w);
      $display(" rw1 = %h", rw1);
      if (rw1 != ~w) /* False */begin
	 f_r1_w1.enq(True);
	 $display(" and128 1 = %h", and128('1,const_wide));
      end
      if (rw1 == ~w) /* True */begin
	 f_r1_w2.enq(True);
	 $display(" and128 2 = %h", and128(17,const_wide));
      end

      Bit#(64) rp1 <- av_poly (p, s, w, n);
      $display(" rp1 = %h", rp1);
      if (rp1 == ~p) /* True */begin
	 f_r1_p1.enq(True);
	 $display(" andN 1 = %h", andN('1,p));
      end
      if (rp1 != ~p) /* False */begin
	 f_r1_p2.enq(True);
	 $display(" andN 2 = %h", andN(17,p));
      end
      state <= state + 1;
   endrule

   // test actions conditional on value function calls
   rule r2 (state == 1);
      $display("Rule r2");

      if (and32(17,const_narrow) == 17) /* True */ begin
	 f_r2_n1.enq(True);
	 $display(" and32 1");
      end
      if (and32(0,const_narrow) == 17) /* False */ begin
	 f_r2_n2.enq(True);
	 $display(" and32 2");
      end

      if (and128(17,const_wide) == 17) /* True */ begin
	 f_r2_w1.enq(True);
	 $display(" and128 1");
      end
      if (and128(0,const_wide) == 17) /* False */ begin
	 f_r2_w2.enq(True);
	 $display(" and128 2");
      end

      if (andN(17,p) == 17) /* True */ begin
	 f_r2_p1.enq(True);
	 $display(" andN 1");
      end
      if (andN(0,p) == 17) /* False */ begin
	 f_r2_p2.enq(True);
	 $display(" andN 2");
      end

      state <= state + 1;
   endrule

   rule done (state == 2);
      $finish(0);
   endrule

endmodule

