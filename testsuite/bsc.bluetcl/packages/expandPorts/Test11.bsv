
typedef struct {
   int a;
   int b;
   } TS deriving(Bits,Eq);

typedef struct {
   int sum;
   bit cry;
   } TSum deriving(Bits,Eq);

interface Test11;
   method Action add( TS s );
   method TSum   sum();
   method Tuple2#(bit,bit) tst( Tuple3#(bit,bit,bit) z );
endinterface


(* synthesize *)
module mkTest11( Test11 );
   Wire#(int) inA <- mkDWire(0);
   Wire#(int) inB <- mkDWire(maxBound);

   method Action add( TS s );
      inA <= s.a;
      inB <= s.b;
   endmethod
   
   method TSum  sum();
      Bit#(33) lsum = zeroExtend(pack(inA)) + zeroExtend(pack(inB));

      int sm = unpack(lsum[31:0]);
      bit cr = lsum[32];
      return TSum { sum:sm, cry:cr };
   endmethod

   method Tuple2#(bit,bit) tst( Tuple3#(bit,bit,bit) z );
      return unpack( {pack(inA)[0], pack(inB)[0]} );
   endmethod

endmodule
