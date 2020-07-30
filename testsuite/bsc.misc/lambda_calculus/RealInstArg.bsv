(* synthesize *)
module mkRealInstArg_Sub #(parameter Real r) ();
   rule doDisp;
      $display(r);
   endrule
endmodule

(* synthesize *)
module sysRealInstArg ();
   Real r = 0.0;
   Empty i <- mkRealInstArg_Sub(r);
endmodule
