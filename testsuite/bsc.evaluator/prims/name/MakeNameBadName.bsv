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
module sysMakeNameBadName (Empty);
   Reg#(Bool) rg <- mkReg(True);
   rule r;
      Bool b = probe("this&#@&*^# is+-#@%^ a bad name", !rg);
      rg <= b;
   endrule
endmodule

