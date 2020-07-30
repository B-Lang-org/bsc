import Connectable::*;
import SenderReceiver::*;

import WrapSender::*;
import WrapReceiver::*;
import WrapConnection::*;

(*synthesize*)
module sysConnect_wrapped2(Empty);
   SingletonInout send <- wrapSender();
   SingletonInout recv <- wrapReceiver();
   wrapConnection(recv.iioo, send.iioo);
   Reg#(int) count <- mkReg(0);
   rule increment;
      count <= count + 1;
   endrule
   
   rule stop (count==1);
      $finish(0);
   endrule
      
endmodule

