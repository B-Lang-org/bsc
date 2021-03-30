// Test that "_" has the right type by expecting a failure on mis-use
module sysModDef_PortArg(Bool _, Empty ifc);
  Reg#(Bit#(8)) rg <- mkReg(_);
endmodule
