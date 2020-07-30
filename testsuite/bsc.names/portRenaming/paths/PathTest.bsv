typedef Bit#(8)  ReqData;
typedef Bit#(16) RespData;

interface IFC;
   method Action put (ReqData x);
   (* ready="req" *)
   method ReqData req_info();
endinterface

(* synthesize *)
module mkPathTestTop ( IFC );

   IFC uut <- mkPathTestSub;

   Reg#(Bit#(3)) stall <- mkReg(0);

   method Action put (ReqData x) if ( stall == 0 );
      uut.put( x );
   endmethod

   method req_info = uut.req_info;
endmodule

(* synthesize *)
module mkPathTestSub( IFC );
   
   Wire#(ReqData)   req_data <- mkWire;

   method ReqData req_info();
      return req_data;
   endmethod

   method Action  put(ReqData d);
      req_data <= d;
   endmethod
      
endmodule

