interface Ifc; 
   method Action request(Bool maddr); 
   method Bool get();
endinterface

(* synthesize *)
module sysMEValueMethod(Ifc);
   
   Reg#(Bool) state <- mkReg(True);
   Reg#(Bool) x <- mkReg(False);   
   Reg#(Bool) req <- mkWire();   

   // this rule is ME with "get" but executes afterward, so Bluesim
   // inserts an inhibitor on the CAN_FIRE of this rule
   rule start_sending_req (!state && req);
      state <= True;
   endrule: start_sending_req

   method Action request(Bool maddr);
      req <= maddr;
   endmethod : request

   method Bool get() if (state);
      return x;
   endmethod: get
  
endmodule

