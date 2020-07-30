(* synthesize *)
module sysFixupRule_NoClock();
   Empty e <- mkFixupRule_NoClock_Sub(clocked_by noClock);
endmodule

module mkFixupRule_NoClock_Sub();
   rule r_disp;
      $display("Hello");
   endrule
endmodule
