interface IFC;
   method Bit#(32) getVal();
endinterface

(* synthesize *)
module sysMethodInternalNameClash (IFC);
   method Bit#(32) getVal();
      Bit#(32) getVal = 0;
      return(getVal);
   endmethod
endmodule

