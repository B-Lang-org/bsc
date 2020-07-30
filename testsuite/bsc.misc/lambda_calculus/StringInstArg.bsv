(* synthesize *)
module mkStringInstArg_Sub #(parameter String s) ();
   rule doDisp;
      $display("%s", s);
   endrule
endmodule

(* synthesize *)
module sysStringInstArg ();
   String s = "Hello";
   Empty i <- mkStringInstArg_Sub(s);
endmodule
