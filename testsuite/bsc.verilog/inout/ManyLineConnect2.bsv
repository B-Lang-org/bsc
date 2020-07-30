import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;
import ArgToIfc::*;
import Vector::*;

typedef 10 Size;

(*synthesize*)
module sysManyLineConnect2(Empty);
   RegisteredSender_ifc send <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver;
   
   Inout#(int) left_endpoint =  send.iioo;
   Inout#(int) right_endpoint = recv.iioo;
   
   Vector#(Size,InoutIFC) inbetween = newVector;
   inbetween[0] <- sysArgToIfc(left_endpoint);
   for(Integer i=1;i<valueOf(Size);i=i+1)
      begin
         inbetween[i]<-sysArgToIfc(inbetween[i-1].i_out);
      end
   
   mkConnection(inbetween[valueOf(Size)-1].i_out,right_endpoint);
   
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
