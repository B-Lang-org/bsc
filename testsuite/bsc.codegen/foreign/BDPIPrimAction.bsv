import "BDPI" function PrimAction my_display (Bit#(8) x);

function Action my_display2(Bit#(8) x);
   let y = my_display(x);
   return fromPrimAction(y);
endfunction

(* synthesize *)
module mkBDPIPrimAction ();
   rule r;
      my_display2(45);
      $finish(0);
   endrule
endmodule
