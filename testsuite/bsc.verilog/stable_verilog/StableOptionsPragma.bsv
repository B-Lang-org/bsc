// regen must honor the module's recorded codegen flags (the .ba carries
// the options pragma): regression for -c taking flags from the .ba
(* synthesize *)
(* options = "-keep-fires" *)
module sysStableOptionsPragma();
   Reg#(UInt#(8)) a <- mkReg(0);
   Reg#(UInt#(8)) b <- mkReg(1);
   rule r1 (a < 100); a <= a + b; endrule
   rule r2 (b < 50); b <= b + 1; endrule
endmodule
