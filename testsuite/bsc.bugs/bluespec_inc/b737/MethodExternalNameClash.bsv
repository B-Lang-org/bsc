interface IFC;
   method Bit#(32) getVal();
endinterface

(* synthesize *)
module sysMethodExternalNameClash (IFC);
   Bit#(32) getVal = 0;
   method Bit#(32) getVal();
      return 17;
   endmethod
endmodule

