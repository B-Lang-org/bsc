interface Ifc;
   method Action meth();
endinterface

(* synthesize *)
module sysShadowInMethod(Ifc);

   Reg#(Maybe#(UInt#(5))) ending <- mkReg(Invalid);
   Reg#(Maybe#(UInt#(5))) lastdata <- mkReg(Invalid);

   Maybe#(UInt#(5)) en = ending;

   method Action meth() if (en matches tagged Valid .m);
      let en = tagged Valid (m+1);
      let mn = tagged Valid (m+1);

      ending <= en;
      lastdata <= mn;
   endmethod

endmodule

