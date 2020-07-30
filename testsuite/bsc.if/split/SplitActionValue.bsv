import GetPut::*;

module test(Get#(Bit#(16)));

  method get();
    actionvalue
      (* split *)
      actionvalue
        return(17);
      endactionvalue
    endactionvalue
   endmethod

endmodule
