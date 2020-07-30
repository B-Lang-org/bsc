interface IFC;
   method Bit#(32) getVal();
   method Bit#(32) getVal2();
endinterface

(* synthesize *)
module sysMethodToMethodReference (IFC);
   method Bit#(32) getVal();
      return 0;
   endmethod
   method Bit#(32) getVal2();
      return(getVal);
   endmethod
endmodule
