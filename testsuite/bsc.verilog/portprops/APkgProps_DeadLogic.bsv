// Test that "unused" propagates backwards through logic which is
// itself unused: log_x feeds a $display (simulation-only) through
// arithmetic, so it drives no hardware.  The APackage-based deduction
// (getIOPropsA) labels it "unused"; getIOProps only traces unusedness
// through direct connections, so it reports no properties for log_x.
// Both label EN_log "unused" (the method's actions create no
// hardware).  This is one of the documented intentional differences.

interface APkgProps_DeadLogic;
   method Action log(Bit#(8) x);
endinterface

(* synthesize *)
module sysAPkgProps_DeadLogic (APkgProps_DeadLogic);
   method Action log(Bit#(8) x);
      Bit#(8) res = x * 3;
      if (res > 10)
         res = res - 1;
      $display("res = %d", res);
   endmethod
endmodule
