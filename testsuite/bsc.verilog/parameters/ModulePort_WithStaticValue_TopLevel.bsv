
(* synthesize *)
module sysModulePort_WithStaticValue_TopLevel #(Bool b) ();
   Reg#(Bool) done <- mkReg(False);

   rule r_disp (!done);
      $display("b = %d", b);
      done <= True;
   endrule

   rule r_done (done);
      $finish(0);
   endrule
endmodule

