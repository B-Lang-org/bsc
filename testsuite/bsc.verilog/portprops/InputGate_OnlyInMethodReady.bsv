
interface Ifc;
   method Action set (Bool b);
endinterface

(* synthesize *)
(* gate_all_clocks *)
module sysInputGate_OnlyInMethodReady (Ifc);

   Reg#(Bool) rg <- mkReg(True) ;

   method Action set ( Bool b );
      rg <= b ;
   endmethod

endmodule
