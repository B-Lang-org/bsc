interface Ifc;
   method Action m();
endinterface

(* synthesize *)
module sysMethodNameShadow(Ifc);

   Reg#(Maybe#(UInt#(5))) ending <- mkReg(Invalid);

   // The pattern variable is the same as the method name!
   method Action m() if (ending matches tagged Valid .m);
      ending <= tagged Valid (m+1);
   endmethod

endmodule

