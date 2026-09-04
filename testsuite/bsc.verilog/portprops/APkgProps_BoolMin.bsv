// Test a ready signal that the two deductions disagree about, in the
// direction where getIOProps concludes more than getIOPropsA.
//
// Both methods have a ready condition that is redundant, but only one
// of the two redundancies is a shape getIOPropsA recognizes:
//
//   RDY_k = (a && b) || !a || !b     a tautology, which getIOPropsA
//                                   reaches through its complementary
//                                   pair rule, so both report "const"
//
//   RDY_m = (a && b) || (!a && b)    minimizes to `b`, a register
//                                   output.  The netlist optimization
//                                   performs the minimization, so
//                                   getIOProps reports "reg";
//                                   getIOPropsA does not attempt
//                                   boolean minimization over
//                                   independent dynamic guards and
//                                   concludes nothing.
//
// This is the mechanism by which a property is lost from a submodule's
// recorded properties and so from a parent's "Ports:" comment.

interface APkgProps_BoolMin;
   method Bit#(8) k();
   method Bit#(8) m();
endinterface

(* synthesize *)
module sysAPkgProps_BoolMin (APkgProps_BoolMin);
   Reg#(Bool) a <- mkReg(False);
   Reg#(Bool) b <- mkReg(False);
   Reg#(Bit#(8)) r <- mkReg(0);

   method Bit#(8) k() if ((a && b) || !a || !b) = r;
   method Bit#(8) m() if ((a && b) || (!a && b)) = r;
endmodule
