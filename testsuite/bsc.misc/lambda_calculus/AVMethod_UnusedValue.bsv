
typedef UInt#(32) T;

interface Ifc;
   method ActionValue#(T) m();
endinterface

(* synthesize *)
module mkAVMethod_UnusedValue_Sub(Ifc);
   Reg#(T) rg <- mkReg(0);

   method ActionValue#(T) m();
      rg <= rg + 1;
      return rg;
   endmethod
endmodule

(* synthesize *)
module sysAVMethod_UnusedValue();
   Ifc s <- mkAVMethod_UnusedValue_Sub;

   rule r;
      let v <- s.m();
   endrule
endmodule

