// Test that "clockOf" works on a module port

(* synthesize *)
module sysModulePort_ResetOf( Reset r2,
			      (* reset_by="r2" *) Bool p,
			      Empty i );

   rule r;
      if ( resetOf(p) == r2 )
	 $display("success");
       else
	 error("clockOf failure");
      $finish(0);
   endrule
endmodule

