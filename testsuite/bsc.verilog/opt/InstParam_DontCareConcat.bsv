(* synthesize *)
module sysInstParam_DontCareConcat();
   // The parameter value for a submodule instantiation contains a don't-care
   // whose value is chosen in ASyntax, so the final value can only be
   // optimized after that point.  Test that a constant appears in the
   // Verilog, instead of a concat of constants.
   //
   Reg#(Bit#(8)) rg <- mkReg({3'b0, ?, 1'b0});
endmodule
