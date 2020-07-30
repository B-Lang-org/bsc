
(* synthesize *)
module sysModulePort_WithStaticValue_TwoLevel ();
   mkModulePort_WithStaticValue_TwoLevel_Sub1(True);
endmodule

(* synthesize *)
module mkModulePort_WithStaticValue_TwoLevel_Sub1#(Bool b) ();
   mkModulePort_WithStaticValue_TwoLevel_Sub2(b);
endmodule

(* synthesize *)
module mkModulePort_WithStaticValue_TwoLevel_Sub2#(Bool b) ();
   Reg#(Bool) done <- mkReg(False);

   rule r_disp (!done);
      $display("b = %d", b);
      done <= True;
   endrule

   rule r_done (done);
      $finish(0);
   endrule
endmodule

