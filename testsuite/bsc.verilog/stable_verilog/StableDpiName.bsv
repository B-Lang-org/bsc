// exclusion guard: a family-shaped imported function name must not be
// renumbered (the C linkage depends on it)
import "BDPI" function Bit#(8) f__h1(Bit#(8) v);

(* synthesize *)
module sysStableDpiName();
   Reg#(Bit#(8)) r <- mkReg(0);
   rule tick;
      r <= f__h1(r);
   endrule
endmodule
