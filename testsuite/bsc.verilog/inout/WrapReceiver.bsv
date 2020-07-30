import SenderReceiver::*;

(*synthesize*)
module wrapReceiver(SingletonInout);
   SingletonInout it <- mkReceiver();
   method Inout#(int) iioo;
      return it.iioo;
   endmethod
endmodule   

