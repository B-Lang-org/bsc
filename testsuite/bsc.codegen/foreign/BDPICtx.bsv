// A numeric proviso on an import "BDPI" declaration: the relationship
// between the widths is enforced by the typechecker at every
// application and then erased -- the C side receives the sizes it
// needs as explicit arguments, per the usual polymorphic-BDPI
// convention.
import "BDPI" function Bit#(m) bit_dup (Bit#(n) x, Bit#(32) nsz)
   provisos(Add#(n, n, m));

function Bit#(m) dup(Bit#(n) x) provisos(Add#(n, n, m));
   return bit_dup(x, fromInteger(valueOf(n)));
endfunction

(* synthesize *)
module mkBDPICtx();
   rule r;
      Bit#(16) y1 = dup(8'h5A);
      Bit#(24) y2 = dup(12'hABC);
      $display("dup8  = %h", y1);
      $display("dup12 = %h", y2);
      $finish(0);
   endrule
endmodule
