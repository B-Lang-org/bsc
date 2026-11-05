// Test that the APackage-based VIOProps deduction (getIOPropsA)
// treats only hardware uses as uses, like getIOProps:
//  - disp_x feeds only a $display (which exists only in simulation),
//    so it is "unused", and so is EN_disp (the method's actions
//    create no hardware)
//  - mixed_x feeds a register's D_IN through a method call that
//    appears inside a $display argument's context, so it is "reg"

interface APkgProps_Foreign;
   method Action disp(Bit#(8) x);
   method ActionValue#(Bit#(8)) mixed(Bit#(8) x);
endinterface

(* synthesize *)
module sysAPkgProps_Foreign (APkgProps_Foreign);
   Reg#(Bit#(8)) r <- mkRegU;

   method Action disp(Bit#(8) x);
      $display("disp %d", x);
   endmethod

   method ActionValue#(Bit#(8)) mixed(Bit#(8) x);
      r <= x;
      $display("mixed %d", r);
      return r;
   endmethod
endmodule
