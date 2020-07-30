interface Ifc;
   method Action m(Bit#(16) b);
endinterface

(* synthesize *)
module sysMethodArg_OneReg (Ifc);
   Reg#(Bit#(16)) rg <- mkReg(0);

   method Action m(b);
      rg <= b;
   endmethod
endmodule

