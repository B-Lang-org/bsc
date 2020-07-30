import Connectable::*;
import RegisteredSender::*;
import EnabledReceiver::*;

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

module mkCond#(Bool choose, Inout#(int) left, 
                 Inout#(int) center, Inout#(int) right)();
   if (choose)
      mkConnection(left,center);
   else
      mkConnection(center,right);
endmodule   

(*synthesize*)
module sysCond(Empty);
   RegisteredSender_ifc send <- mkRegisteredSender;
   RegisteredSender_ifc send2 <- mkRegisteredSender;
   EnabledReceiver_ifc recv <- mkEnabledReceiver;
   mkCond((fibo(10)==55),send2.iioo, recv.iioo, send.iioo);
   Reg#(int) count <- mkReg(0);
   rule increment;
      count <= count + 1;
      send.set(count);
      send2.set(count*100);
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
