import Methods::*;
import NoInline::*;

typedef enum { S0_Action, S1_ActionValue, S2_Value } State
   deriving (Eq, Bits);

(* synthesize *)
module sysTb ();

   Ifc gcd <- sysMethods;

   Reg#(T) c1 <- mkReg(19);
   Reg#(T) c2 <- mkReg(5);

   Reg#(T) rg <- mkReg(0);

   Reg#(State) state <- mkReg(S0_Action);

   function Action store_res(T res);
      action
         // Operate on the value to force defs between actions
         rg <= (res + 1) * 2;
      endaction
   endfunction

   Action upd_inps =
      action
         // Test the use of noinline functions
         c1 <= add(c1, 3);
         c2 <= add(c2, 2);
      endaction;

   // Test calls of the various method types
   rule r0 (state == S0_Action);
      gcd.start(c1,c2);
      upd_inps;
      state <= S1_ActionValue;
   endrule

   rule r1 (state == S1_ActionValue);
      let res <- gcd.start_and_result(c1,c2);
      store_res(res);
      upd_inps;
      state <= S2_Value;
   endrule

   rule r2 (state == S2_Value);
      let res = gcd.result();
      store_res(res);
      state <= S0_Action;
   endrule

   rule exit (c1 > 100);
      // Test system tasks, their arguments, and return values
      let t <- $time();
      $display(t, "Hello");
      $finish(0);
   endrule

endmodule
