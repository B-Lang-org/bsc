// This example makes two clocks, where one is a gated version of
// the other (using mkGatedClock).

import Clocks::*;

// Clock period
Integer p1 = 10;

// the initial value of the registers will be AA
Bit#(8) init_val = 8'hAA;

// function to make $stime the same for Bluesim and Verilog
function ActionValue#(Bit#(32)) adj_stime(Integer p);
   actionvalue
      let adj = (p + 1) / 2;
      let t <- $stime();
      if (genVerilog)
	 return (t + fromInteger(adj));
      else
	 return t;
   endactionvalue
endfunction

(* synthesize *)
module sysGatedClock_TwoModTwoSyn ();
   // clk1 counter
   Reg#(Bit#(8)) counter <- mkReg(0);

   // create the gate condition
   GatedClockIfc g1 <- mkGatedClockFromCC(True);
   Reg#(Bit#(8)) gate_diff <- mkReg(1);
   Reg#(Bit#(8)) gate_count <- mkReg(0);
   (* fire_when_enabled *)
   rule update_gate (gate_count == counter);
      Bool gate_on = (gate_count[0] == 0);
      g1.setGateCond(gate_on);
      gate_count <= gate_count + gate_diff;
      gate_diff <= gate_diff + 1;
   endrule
   Clock clk1 = g1.new_clk;

   SubIfc s
       <- mkGatedClock_TwoModTwoSyn_Sub(clocked_by clk1, reset_by noReset);

   (* fire_when_enabled *)
   rule tick;
      counter <= counter + 1;
      $display("(%d) counter = %h, rg1 = %h, rg2 = %h",
	       adj_stime(p1), counter, s.read_rg1, s.read_rg2);
      if (s.read_rg2 > (init_val + 17))
	 $finish(0);
   endrule

endmodule


interface SubIfc;
   method Bit#(8) read_rg1();
   method Bit#(8) read_rg2();
endinterface

(* synthesize *)
(* gate_input_clocks = "default_clock" *)
module mkGatedClock_TwoModTwoSyn_Sub (SubIfc);

   GatedClockIfc g2 <- mkGatedClockFromCC(False);
   Reg#(Bit#(8)) rg1 <- mkRegU;
   (* fire_when_enabled *)
   rule r1;
      rg1 <= rg1 + 1;
      g2.setGateCond(!g2.getGateCond);
   endrule
   Clock clk2 = g2.new_clk;

   // avoid the need for reset
   Reg#(Bit#(8)) rg2 <- mkRegU(clocked_by clk2);
   (* fire_when_enabled *)
   rule r2;
      rg2 <= rg2 + 1;
   endrule

   method read_rg1 = rg1;
   method read_rg2 = rg2;

endmodule
