// __f family + noinline instance naming
(* noinline *)
function Bit#(16) nadd(Bit#(16) p, Bit#(16) q) = p + q + 3;

(* synthesize *)
module sysStableNoInline();
   Reg#(Bit#(16)) a <- mkReg(0);
   Reg#(Bit#(16)) b <- mkReg(1);
   rule r1; a <= nadd(a, b); endrule
   rule r2; b <= nadd(b, 16'd7); endrule
endmodule
