import Vector :: *;

interface Ifc;
   method Action write(UInt#(3) idx, UInt#(8) val);
   method UInt#(8) read(UInt#(3) idx);
endinterface

(* synthesize *)
module sysRegOfVec(Ifc);
   Reg#(Vector#(8, UInt#(8))) rg <- mkReg(replicate(0));

   method Action write(UInt#(3) idx, UInt#(8) val);
      rg[idx] <= val;
   endmethod

   method UInt#(8) read(UInt#(3) idx) = rg[idx];
endmodule

