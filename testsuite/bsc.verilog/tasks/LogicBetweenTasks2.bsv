// -------------------------

interface Ifc;
  method Bit#(32) m(Bit#(32) x);
endinterface

(* synthesize *)
module mkLogicBetweenTasks2_Sub (Ifc);
   Reg#(Bit#(32)) rg <- mkReg('1);
   method m(x) = ~x & rg;
endmodule

// -------------------------

(* synthesize *)
module sysLogicBetweenTasks2 ();
   Reg#(Bit#(32)) state <- mkReg(0);

   Ifc sub <- mkLogicBetweenTasks2_Sub;

   rule r1 (state == 0);
      let v1 <- $stime();
      $display("v1 = %b", v1);

      // test when the logic is in a separately synthesized module
      let s1 = sub.m(v1);
      $display("s1 = %b", s1);
      $display();

      state <= state + 1;
   endrule

   rule r2 (state == 1);
      $finish(0);
   endrule

endmodule
