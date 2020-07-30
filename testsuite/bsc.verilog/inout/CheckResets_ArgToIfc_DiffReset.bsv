import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;
import ArgToIfc::*;

(*synthesize*)
module sysCheckResets_ArgToIfc_DiffReset(Reset r2, Empty i);

   RegisteredSender_ifc send <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver(reset_by r2);

   // This fails because "send" is on "no_reset" and this module is on
   // the default reset.
   InoutIFC x1 <- sysArgToIfc(send.iioo);

   // This fails because "x1" is on the default reset and "recv" is on "r2"
   mkConnection(x1.i_out,recv.iioo);
      
endmodule

