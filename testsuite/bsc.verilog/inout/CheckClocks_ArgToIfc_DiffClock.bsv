import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;
import ArgToIfc::*;

(*synthesize*)
module sysCheckClocks_ArgToIfc_DiffClock(Clock c2, Empty i);

   RegisteredSender_ifc send <- mkRegisteredSender;
   EnabledReceiver_ifc recv
       <- mkEnabledReceiver(clocked_by c2, reset_by noReset);

   InoutIFC x1 <- sysArgToIfc(send.iioo, reset_by noReset);
   mkConnection(x1.i_out,recv.iioo);
      
endmodule

