import Clocks::*;

// This is not too different from GatedClock_TwoModTwoSyn, except that the
// source of the gated clock (clk2) is laundered through a synthesis boundary.

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
module sysSubRule();
   Reg#(Bit#(8)) counter <- mkReg(0);

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

   Ifc s <- mkSubRule(clocked_by clk1);

   // avoid the need for reset
   Reg#(Bit#(8)) rg1 <- mkRegU(clocked_by clk1);

   (* fire_when_enabled *)
   rule r1;
      rg1 <= rg1 + 1;
      s.g2.setGateCond(!s.g2.getGateCond);
   endrule

   (* fire_when_enabled *)
   rule tick;
      counter <= counter + 1;
      $display("(%d) counter = %h, rg1 = %h, rg2 = %h",
               adj_stime(p1), counter, rg1, s.rg2);
      if (s.rg2 > (init_val + 17))
         $finish(0);
   endrule
endmodule

interface Ifc;
   interface GatedClockIfc g2;
   interface ReadOnly#(Bit#(8)) rg2;
endinterface

(* synthesize *)
module mkSubRule(Ifc);
   GatedClockIfc sg <- mkSubRule_Gate();
   Clock sclk = sg.new_clk;

   // avoid the need for reset
   Reg#(Bit#(8)) srg <- mkRegU(clocked_by sclk);

   (* fire_when_enabled *)
   rule sr;
      srg <= srg + 1;
   endrule

   interface g2 = sg;
   interface rg2 = regToReadOnly(srg);
endmodule

(* synthesize *)
module mkSubRule_Gate(GatedClockIfc);
   GatedClockIfc ssg <- mkGatedClockFromCC(False);
   return ssg;
endmodule

