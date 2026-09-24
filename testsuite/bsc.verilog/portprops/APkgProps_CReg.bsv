// Test the APackage-based VIOProps deduction (getIOPropsA) through
// inlined CReg instances, compared with the ASPackage-based deduction
// (getIOProps):
//  - rdA0 reads port 0 of crA: the retained register's output, "reg"
//  - rdA1 reads port 1 of crA: a bypass mux with port 0's write, so
//    no properties
//  - rdB1 reads port 1 of crB, whose port 0 is never written: the
//    bypass reduces away, leaving the register output, "reg"
//  - wrA0_v feeds the register through the bypass chain: used, but no
//    direct connection

interface APkgProps_CReg;
   method Bit#(8) rdA0();
   method Bit#(8) rdA1();
   method Bit#(8) rdB1();
   method Action wrA0(Bit#(8) v);
endinterface

(* synthesize *)
module sysAPkgProps_CReg (APkgProps_CReg);
   Reg#(Bit#(8)) crA[2] <- mkCReg(2, 0);
   Reg#(Bit#(8)) crB[2] <- mkCReg(2, 0);

   method rdA0 = crA[0];
   method rdA1 = crA[1];
   method rdB1 = crB[1];

   method Action wrA0(Bit#(8) v);
      crA[0] <= v;
   endmethod
endmodule
