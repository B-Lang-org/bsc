interface Ifc;
   method Action incr();
endinterface

(* synthesize *)
module sysRuleMethClash (Ifc);
   Reg#(UInt#(16)) rg <- mkReg(0);

   rule incr;
      rg <= rg + 1;
   endrule

   Ifc i = interface Ifc;
              method Action incr();
                 rg <= rg + 2;
              endmethod
           endinterface;

   return i;
endmodule

