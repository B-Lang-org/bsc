// Regression test for quadratic behaviour in InlineCReg (creg phase)
// and AVerilog.ds7 (verilog phase) and AExpand.aoptExpandTest (aopt phase).
//
// Many CRegs each with a trivial rule.  Without the corresponding fixes,
// the creg / verilog / aopt phases become quadratic in the number of
// CReg port methods and the compile takes orders of magnitude longer.
package CregInlineBlowup;

typedef 4096 NCregs;
Integer nports = 4;

(* synthesize *)
module mkCregInlineBlowup (Empty);
   for (Integer i = 0; i < valueOf(NCregs); i = i + 1) begin
      Reg#(Bit#(8)) cr[nports] <- mkCReg(nports, 0);
      rule rstep;
         cr[0] <= cr[0] + 1;
      endrule
   end
endmodule

endpackage
