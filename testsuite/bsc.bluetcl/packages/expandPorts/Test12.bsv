(* always_ready *)
interface Test12;
   method Action   add( int a );
   method Bit#(0)  advance();  // just want the ready signal
endinterface

(* synthesize *)
module mkTest12( Test12 );
   Reg#(Bit#(0)) cond <- mkRegU;
   Reg#(int)  regA <- mkRegU;

   method Action add( int a );
      regA <= a;
   endmethod

   method Bit#(0)   advance();  // just want the ready signal
      return cond;
   endmethod
      
endmodule
