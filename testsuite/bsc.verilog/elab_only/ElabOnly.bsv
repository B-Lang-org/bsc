// Fixtures for the -elab-only flag (a -verilog compile that writes
// only .ba files, deferring the .v to -c or the linking stage)

(* synthesize *)
module mkESub(Reg#(Bit#(8)));
   Reg#(Bit#(8)) rg <- mkReg(0);
   return rg;
endmodule

(* synthesize *)
module sysETb(Empty);
   Reg#(Bit#(8)) sub <- mkESub;
   Reg#(Bit#(4)) n <- mkReg(0);
   rule bump;
      sub <= sub + 2;
      n <= n + 1;
      if (n == 4) begin
         $display("sub = %0d", sub);
         $finish(0);
      end
   endrule
endmodule
