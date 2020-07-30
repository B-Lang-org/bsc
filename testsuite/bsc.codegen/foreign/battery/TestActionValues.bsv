import ActionValueImports::*;
import ValueImports::*;

// for replicate
import ListN::*;

typedef enum { DoFuncs, ShowRegs, Finish } State deriving (Eq, Bits);

(* synthesize *)
module mkTestActionValues ();
   Reg#(State) state <- mkReg(DoFuncs);

   // static inputs
   Bit#(128) w1 = const_wide;
   Bit#(128) w2 = ~w1;
   Bit#(32) n1 = 64;
   Bit#(64) p1 = {const_narrow, const_narrow};
   Bit#(32) n2 = 96;
   Bit#(96) p2 = {const_narrow, const_narrow, const_narrow};
   String s = "Hi mom!";

   // dynamic inputs (except String)
   Reg#(Bit#(128)) w3 <- mkReg({32'd17, 32'd17, 32'd17, 32'd17});
   Reg#(Bit#(32)) n3 <- mkReg(64);
   Reg#(Bit#(64)) p3 <- mkReg({32'd17, 32'd17});
   String s3 = "Hi mom!";

   // storage for results
   Reg#(Bit#(32)) res_n1 <- mkReg(0);
   Reg#(Bit#(128)) res_w1 <- mkReg(0);
   Reg#(Bit#(64)) res_p1 <- mkReg(0);

   Reg#(Bit#(32)) res_n2 <- mkReg(0);
   Reg#(Bit#(128)) res_w2 <- mkReg(0);
   Reg#(Bit#(64)) res_p2 <- mkReg(0);

   Reg#(Bit#(128)) res_w3 <- mkReg(0);
   Reg#(Bit#(64)) res_p3 <- mkReg(0);

   rule disp (state == DoFuncs);
      srandom(n1);
      $display("Foreign Function Calls");

      // ---------------
      // static inputs
      
      Bit#(32) rn1 <- av_narrow (w1, p1, n1, s);
      $display(" rn1 = %h", rn1);
      Bit#(32) rn2 <- av_narrow (w2, p2, n2, s);
      $display(" rn2 = %h", rn2);

      Bit#(128) rw1 <- av_wide (s, n1, p1, w1);
      $display(" rw1 = %h", rw1);
      Bit#(128) rw2 <- av_wide (s, n2, p2, w2);
      $display(" rw2 = %h", rw2);

      Bit#(64) rp1 <- av_poly (p1, s, w1, n1);
      $display(" rp1 = %h", rp1);
      Bit#(96) rp2 <- av_poly (p2, s, w2, n2);
      $display(" rp2 = %h", rp2);
      // also test a smaller return value
      Bit#(32) rp0 <- av_poly (const_narrow, s, w1, 32);
      $display(" rp0 = %h", rp0);

      Bit#(32) no_arg_n <- random_narrow();
      $display(" no_arg_n = %h", no_arg_n);

      Bit#(128) no_arg_w <- random_wide();
      $display(" no_arg_w = %h", no_arg_w);

      // ---------------
      // dynamic inputs (and writing outputs to registers)
      
      Bit#(32) rn3 <- av_narrow (w3, p3, n3, s3);
      $display(" rn3 = %h", rn3);
      res_n1 <= rn3;

      Bit#(128) rw3 <- av_wide (s3, n3, p3, w3);
      $display(" rw3 = %h", rw3);
      res_w1 <= rw3;

      Bit#(64) rp3 <- av_poly (p3, s3, w3, n3);
      $display(" rp3 = %h", rp3);
      res_p1 <= rp3;

      // ---------------
      // foreign func inputs
      // take the outputs of the first round of foreign funcs as inputs

      Bit#(32) fn = rn1 * rn1; /* == 64 */

      Bit#(32) rn4 <- av_narrow (rw1, rp1, fn, s);
      $display(" rn4 = %h", rn4);
      res_n2 <= rn4;

      Bit#(128) rw4 <- av_wide (s, fn, rp1, rw1);
      $display(" rw4 = %h", rw4);
      res_w2 <= rw4;

      Bit#(64) rp4 <- av_poly (rp1, s, rw1, fn);
      $display(" rp4 = %h", rp4);
      res_p2 <= rp4;

      // ---------------
      // system task inputs
      // (use $test$plusargs, for predictability)

      String s5 = "Hi";
      Bool b1 <- $test$plusargs(s5); // True
      // this also tests some logic on the result
      Bit#(128) w5 = zeroExtend(pack(b1));
      Bit#(64) p5 = pack(replicate(b1));
      Bit#(128) rw5 <- av_wide(s5, 64, p5, w5);
      res_w3 <= rw5;

      String s6 = "Hello";
      Bool b2 <- $test$plusargs(s6); // False
      // this also tests some logic on the result
      Bit#(128) w6 = zeroExtend(pack(b2));
      Bit#(64) p6 = pack(replicate(b2));
      Bit#(64) rp6 <- av_poly(p6, s6, w6, 64);
      res_p3 <= rp6;

      $display("");

      state <= ShowRegs;
   endrule

   rule show_regs (state == ShowRegs);
      $display("Register contents");

      $display(" res_n1 = %h", res_n1);
      $display(" res_w1 = %h", res_w1);
      $display(" res_p1 = %h", res_p1);

      $display(" res_n2 = %h", res_n2);
      $display(" res_w2 = %h", res_w2);
      $display(" res_p2 = %h", res_p2);

      $display(" res_w3 = %h", res_w3);
      $display(" res_p3 = %h", res_p3);

      state <= Finish;
   endrule

   rule fin (state == Finish);
      $finish(0);
   endrule

endmodule

