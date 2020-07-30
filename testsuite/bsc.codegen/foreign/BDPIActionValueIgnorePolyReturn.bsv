import "BDPI" function ActionValue#(Bit#(n)) poly_action(Bit#(n) x, Bit#(32) n);

function Action poly(Bit#(n) arg);
  action
    let r <- poly_action(arg, fromInteger(valueOf(n)));
  endaction
endfunction: poly

(* synthesize *)
module mkBDPIActionValueIgnorePolyReturn ();
   rule r;
      poly(7'h1a);
      $finish(0);
   endrule
endmodule
