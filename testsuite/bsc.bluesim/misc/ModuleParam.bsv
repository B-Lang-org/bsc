(* synthesize *)
module sysModuleParam#(parameter UInt#(12) param)(Empty ifc);
   rule r;
      $display("param = %0d", param);
      $finish(0);
   endrule: r
endmodule: sysModuleParam
