import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;

// test whether inouts survive being passed around higher-order functions
function Inout#(a) higherfunc(function Inout#(a) f(b bparam) , b x);
   return f(x);
endfunction

function (function Inout#(a) bfunc(Bool bparam)) lowerfunc(Inout#(a) ain);
   function retfunc(bparam) = ain;
   return retfunc;
endfunction
          

(*synthesize*)
module sysHigherFunction(Empty);
   RegisteredSender_ifc send <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver;
   mkConnection(higherfunc(lowerfunc(recv.iioo),True), send.iioo);  //flip me
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
