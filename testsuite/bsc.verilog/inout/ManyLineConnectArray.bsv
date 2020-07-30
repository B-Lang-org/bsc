import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;
import ArgToIfc::*;
import Vector::*;

Integer iSize=10;

(*synthesize*)
module sysManyLineConnectArray(Empty);
   RegisteredSender_ifc send <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver;
   
   Inout#(int) left_endpoint =  recv.iioo;
   Inout#(int) right_endpoint = send.iioo;
   
   //Vector#(Size,InoutIFC) inbetween = newVector;
   InoutIFC inbetween[iSize];
   inbetween[0] <- sysArgToIfc(left_endpoint);
   for(Integer i=1;i<iSize;i=i+1)
      begin
         inbetween[i]<-sysArgToIfc(inbetween[i-1].i_out);
      end
   
   mkConnection(inbetween[iSize-1].i_out,right_endpoint);
   
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
