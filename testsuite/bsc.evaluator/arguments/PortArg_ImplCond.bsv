(* synthesize *)
module sysPortArg_ImplCond ();
   // This has an implicit conditions
   Wire#(Bool) w <- mkWire;

   // The instantiation with an illegal argument expression
   Empty s <- mkPortArg_ImplCond_Sub(w);

   // driver for the wire
   Reg#(Bool) b <- mkReg(True);
   rule r (b);
      w <= True;
      b <= False;
   endrule
endmodule

(* synthesize *)
module mkPortArg_ImplCond_Sub #(Bool b) ();
   rule r;
      $display(b);
   endrule
endmodule
