import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;
import ArgToIfc::*;

(*synthesize*)
module sysLineConnect(Empty);
   RegisteredSender_ifc send <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver;
   InoutIFC x1 <- sysArgToIfc(send.iioo);
   mkConnection(x1.i_out,recv.iioo);

   Reg#(int) count <- mkReg(0);
   rule increment;
      count <= count + 1;
      send.set(count);
   endrule
   
   rule disp (count>0);
      recv.display_it;
   endrule
   
   rule stop (count==10);
      $finish(0);
   endrule
      
endmodule
