import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;

//test whether inouts can be properly passed as function arguments
function Inout#(a) chooseinout(Inout#(a) x, Inout#(a) y);
   if (fibo(10) == 55)
      return x;
   else
      return y;
endfunction

// test the evaluator a little bit
function Integer fibo(Integer n);
   Integer a=0;
   Integer b=1;
   Integer count=1;
   while (count < n)
      begin
         Integer c=a+b;
         a=b;
         b=c;
         count = count + 1;
      end
   fibo = b;
endfunction

(*synthesize*)
module sysFunctionInout(Empty);
   RegisteredSender_ifc send <- mkRegisteredSender;
   RegisteredSender_ifc send2 <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver;
   mkConnection(recv.iioo, chooseinout(send2.iioo,send.iioo));  //flip me
   Reg#(int) count <- mkReg(0);
   rule increment;
      count <= count + 1;
      send.set(count);
      send2.set(count*10);
   endrule
   
   rule disp (count>0);
      recv.display_it;
   endrule
   
   rule stop (count==10);
      $finish(0);
   endrule

/*   
   rule fibos;
      $display("fibo = %d", fibo(10));
   endrule
   */    
   
endmodule
