interface Ifc;
   interface Clock outclk;
endinterface

(* synthesize *)
module sysOutputNoClock();
   Ifc i <- mkOutputNoClock_Sub1;

   Reg#(Bool) is_done <- mkReg(False);

   Reg#(Bit#(8)) counter1 <- mkReg(0);
   Reg#(Bit#(8)) counter2 <- mkRegU(clocked_by i.outclk);

   rule do_display1 (! is_done);
      if (counter1 < 10) begin
         $display("CLK incr");
	 counter1 <= counter1 + 1;
      end
      else
         is_done <= True;
   endrule

   // This rule should not execute, because the clock is noClock
   rule do_display2 (counter2 < 10);
      $display("NoClock incr");
      counter2 <= counter2 + 1;
   endrule

   rule do_finish (is_done);
      $finish(0);
   endrule
endmodule

// This extra synthesis boundary is needed to reveal a Bluesim bug
(* synthesize *)
module mkOutputNoClock_Sub1(Ifc ifc);
   Ifc i <- mkOutputNoClock_Sub2;
   interface outclk = i.outclk;
endmodule

// This leaf module has an output clock defined as "noClock"
(* synthesize *)
module mkOutputNoClock_Sub2(Ifc ifc);
   interface outclk = noClock;
endmodule
