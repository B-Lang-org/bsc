interface IFC;
   method Bit#(32) getVal();
endinterface

(* synthesize *)
module sysMethodSelfReference (IFC);
   method Bit#(32) getVal();
      return(getVal);
   endmethod
endmodule

