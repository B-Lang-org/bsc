// Testbench: run a design whose submodule .v can be regenerated with -c
import GenMode::*;

(* synthesize *)
module sysGenModeTb(Empty);
   Reg#(Bit#(8)) sub <- mkGenSub;
   Reg#(Bit#(4)) n <- mkReg(0);
   rule bump;
      sub <= sub + 2;
      n <= n + 1;
      if (n == 5) begin
         $display("sub = %0d", sub);
         $finish(0);
      end
   endrule
endmodule
