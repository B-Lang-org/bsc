import ActionValueImports::*;
import ValueImports::*;

typedef enum { DoFuncs, Finish } State deriving (Eq, Bits);

(* synthesize *)
module mkTestActionValuesUnusedValue ();
   Reg#(State) state <- mkReg(DoFuncs);

   // static inputs
   Bit#(128) w1 = const_wide;
   Bit#(128) w2 = ~w1;
   Bit#(32) n1 = 64;
   Bit#(64) p1 = {const_narrow, const_narrow};
   Bit#(32) n2 = 96;
   Bit#(96) p2 = {const_narrow, const_narrow, const_narrow};
   String s = "Hi mom!";

   rule disp (state == DoFuncs);
      $display("Foreign Function Calls");

      Bit#(32) rn1 <- av_narrow (w1, p1, n1, s);
      Bit#(128) rw1 <- av_wide (s, n1, p1, w1);
      Bit#(96) rp2 <- av_poly (p2, s, w2, n2);

      state <= Finish;
   endrule

   rule fin (state == Finish);
      $finish(0);
   endrule

endmodule

