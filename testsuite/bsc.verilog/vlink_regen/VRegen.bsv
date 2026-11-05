// Fixtures for link-time regeneration of Verilog from .ba

(* synthesize *)
module mkRSub(Reg#(Bit#(8)));
   Reg#(Bit#(8)) rg <- mkReg(0);
   return rg;
endmodule

(* synthesize *)
module sysVRegenTb(Empty);
   Reg#(Bit#(8)) sub <- mkRSub;
   Reg#(Bit#(4)) n <- mkReg(0);
   rule bump;
      sub <= sub + 3;
      n <= n + 1;
      if (n == 4) begin
         $display("sub = %0d", sub);
         $finish(0);
      end
   endrule
endmodule
