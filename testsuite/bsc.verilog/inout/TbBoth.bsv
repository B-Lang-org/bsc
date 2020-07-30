import BothSendAndReceive::*;
import SenderReceiver::*;
import Connectable::*;
import Vector::*;

typedef 3 Size;

function Inout#(int) getiioo(SingletonInout x);
   return x.iioo;
endfunction

(*synthesize*)
module sysTbBoth();

   Vector#(Size,SingletonInout) duts=newVector;
   duts[0] <- wrapBoth1;
   duts[1] <- wrapBoth2;
   duts[2] <- wrapBoth3;
   Vector#(Size,Inout#(int)) ios=map(getiioo,duts);
   
   mkConnection(ios[0],ios[1]);
   mkConnection(ios[1],ios[2]);
   Reg#(int) count<-mkReg(0);
   rule inc;
      count <= count + 1;
   endrule

   /*   
   rule disp;
      $display("clock ",count);
   endrule
   */ 
   
   rule done (count==60);
      $finish(0);
   endrule
endmodule

(*synthesize*)
module wrapBoth1(SingletonInout);
   //reading on the negedge of 3 is right after the write at the posedge of 2
   SingletonInout x <- mkBoth(101,0,3,4);
   method Inout#(int) iioo();
      return x.iioo;
   endmethod
endmodule
                  
(*synthesize*)
module wrapBoth2(SingletonInout);
   //reading on the negedge of 1 is right after the write at the posedge of 0
   SingletonInout x <- mkBoth(102,1,1,4);
   method Inout#(int) iioo();
      return x.iioo;
   endmethod
endmodule
                  
(*synthesize*)
module wrapBoth3(SingletonInout);
   SingletonInout x <- mkBoth(103,2,2,4);
   method Inout#(int) iioo();
      return x.iioo;
   endmethod
endmodule
                  
