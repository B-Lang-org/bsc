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
module sysMethodTrue();
   Reg#(Bit#(8)) counter <- mkReg(0);

   // Instantiate with a clock whose gate is constant True
   Ifc s <- mkMethodTrue;

   (* fire_when_enabled *)
   rule r;
      s.rg <= s.rg + 1;
   endrule

   (* fire_when_enabled *)
   rule tick;
      counter <= counter + 1;
      $display("(%d) counter = %h, rg = %h",
               adj_stime(p1), counter, s.rg);
      if (counter == 17)
         $finish(0);
   endrule
endmodule

interface Ifc;
   interface Reg#(Bit#(8)) rg;
endinterface

(* synthesize, gate_all_clocks *)
module mkMethodTrue(Ifc);
   // avoid the need for reset
   Reg#(Bit#(8)) srg <- mkRegU;

   interface rg = srg;
endmodule

