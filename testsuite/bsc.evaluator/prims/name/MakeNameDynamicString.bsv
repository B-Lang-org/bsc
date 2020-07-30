import Probe::*;

module [Module] wrapProbe #(t val) (t) provisos (Bits#(t,st));
   Probe#(t) __p <- mkProbe;
   rule doProbe;
      __p <= val;
   endrule
   return val;
endmodule

function t probe(String str, t x) provisos (Bits#(t,st));
   Clock clk = clockOf(x);
   Reset rst = resetOf(x);
   Name__ n = primMakeName(str, noPosition);
   return (primBuildModule(n, clk, rst, wrapProbe(x)));
endfunction

(* synthesize *)
module sysMakeNameDynamicString (Empty);
   Reg#(Bool) rg <- mkReg(True);
   rule r;
      String str = rg ? "bp" : "bn" ;
      Bool b = probe(str, !rg);
      rg <= b;
   endrule
endmodule

