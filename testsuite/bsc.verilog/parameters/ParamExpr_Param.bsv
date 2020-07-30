(* synthesize *)
module sysParamExpr_Param ();
   mkParamExpr_Param_Sub1(True);
endmodule

(* synthesize *)
module mkParamExpr_Param_Sub1#(parameter Bool foo) ();
   mkParamExpr_Param_Sub2(foo);
endmodule

(* synthesize *)
module mkParamExpr_Param_Sub2#(parameter Bool b) ();
   Reg#(Bool) done <- mkReg(False);

   rule r_disp (!done);
      $display("b = %d", b);
      done <= True;
   endrule

   rule r_done (done);
      $finish(0);
   endrule
endmodule

