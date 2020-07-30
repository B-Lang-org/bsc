import ActionImports::*;
import ValueImports::*;

// for replicate
import ListN::*;

(* synthesize *)
module mkTestActions ();
   Reg#(Bool) b <- mkReg(True);

   // constant inputs
   Bit#(32) n = 64;
   Bit#(128) w = {n, 2*n + n, 4*n + n, 5*n + n};
   Bit#(64) p = {n, n + 1};
   String s = "Hi mom!";

   // dynamic inputs (except String)
   Reg#(Bit#(32)) n2 <- mkReg(96);
   Reg#(Bit#(128)) w2 <- mkReg ({n, 2*n + n, 4*n + n, 5*n + n});
   Reg#(Bit#(96)) p2 <- mkReg({n, n + 1, n + 2});
   String s2 = "Hi mom!";

   // foreign function inputs (except String)
   Bit#(32) n3 = andN(64,64);
   Bit#(128) w3 = const_wide;
   Bit#(64) p3 = {const_narrow, const_narrow};
   String s3 = "Hi mom!";

   rule disp (b);
      // no inputs
      tick();

      // constant inputs
      action_function(n,w,p,s);

      // dynamic inputs
      action_function(n2,w2,p2,s2);

      // foreign func inputs
      action_function(n3,w3,p3,s3);

      // system task inputs
      // (use $test$plusargs, for predictability)

      String s4 = "Hi";
      Bool b1 <- $test$plusargs(s4); // True
      // this also tests some logic on the result
      Bit#(128) w4 = zeroExtend(pack(b1));
      Bit#(64) p4 = pack(replicate(b1));
      action_function(64,w4,p4,s4);

      String s5 = "Hello";
      Bool b2 <- $test$plusargs(s5); // False
      // this also tests some logic on the result
      Bit#(128) w5 = zeroExtend(pack(b2));
      Bit#(64) p5 = pack(replicate(b2));
      action_function(64,w5,p5,s5);

      b <= False;
   endrule

   rule fin (!b);
      $finish(0);
   endrule

endmodule

	       
