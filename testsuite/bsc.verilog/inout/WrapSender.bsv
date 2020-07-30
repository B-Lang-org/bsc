import SenderReceiver::*;

(*synthesize*)
module wrapSender(SingletonInout);
   SingletonInout it <- mkSender(`value);
   method Inout#(int) iioo;
      return it.iioo;
   endmethod
endmodule

