import Connectable::*;
import SenderReceiver::*;

(*synthesize*)
module sysConnect_wrapped(Empty);
   SingletonInout send <- mkSender(`value);
   SingletonInout recv <- mkReceiver();
   mkDevice(recv.iioo, send.iioo);
   Reg#(int) count <- mkReg(0);
   rule increment;
      count <= count + 1;
   endrule
   
   rule stop (count==1);
      $finish(0);
   endrule
      
endmodule

(*synthesize*)
module mkDevice#(Inout#(int) recv, Inout#(int) send)();
      mkConnection(recv, send);  //flip me
endmodule: mkDevice
