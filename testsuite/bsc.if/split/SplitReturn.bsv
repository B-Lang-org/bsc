import GetPut::*;

module test(Get#(Bit#(16)));

  method ActionValue#(Bit#(16)) get;
     (* split *)
     return(17);
  endmethod

endmodule
