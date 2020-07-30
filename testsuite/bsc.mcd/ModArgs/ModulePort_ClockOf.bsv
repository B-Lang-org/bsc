// Test that "clockOf" works on a module port

(* synthesize *)
module sysModulePort_ClockOf( Clock c2,
			      (* clocked_by="c2" *) Bool p,
			      Empty i );

   rule r;
      if ( clockOf(p) == c2 )
	 $display("success");
       else
	 error("clockOf failure");
      $finish(0);
   endrule
endmodule

