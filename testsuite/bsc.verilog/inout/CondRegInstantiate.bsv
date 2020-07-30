import Connectable::*;

(*synthesize*)
module sysCondRegInstantiate#(Inout#(Bool) x, Inout#(Bool) y, Inout#(Bool) z)();
   Reg#(Bool) b <- mkRegU();
   mkBranch(b,x,y,z);
endmodule

module mkBranch#(Bool choose, Inout#(Bool) left, 
                 Inout#(Bool) center, Inout#(Bool) right)();
   if (choose)
      mkConnection(left,center);
   else
      mkConnection(center,right);
endmodule
      
   
