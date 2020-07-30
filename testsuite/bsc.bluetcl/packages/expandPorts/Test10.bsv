
typedef struct {
   int a;
   int b;
   } TS deriving(Bits,Eq);

interface Test10;
   method Action add( TS s );
   method int    sum();
endinterface


(* synthesize *)
module mkTest10( Test10 );
   Reg#(int) sm <- mkReg(0);

   Wire#(int) inA <- mkDWire(0);
   Wire#(int) inB <- mkDWire(maxBound);

   method Action add( TS s );
      inA <= s.a;
      inB <= s.b;
   endmethod
   
   method int    sum();
      return inA + inB;
   endmethod

endmodule
