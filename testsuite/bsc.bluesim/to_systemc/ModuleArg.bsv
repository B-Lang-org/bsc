(* synthesize *)
module sysModuleArg(UInt#(12) arg, Empty ifc);
   rule r;
      $display("arg = %0d", arg);
      $finish(0);
   endrule: r
endmodule: sysModuleArg
