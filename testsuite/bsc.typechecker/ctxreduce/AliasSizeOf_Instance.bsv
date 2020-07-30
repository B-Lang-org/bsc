
import LFSR::*;
import Vector::*;

// LFSR sequence generators for the required sizes
//
typeclass DataLFSR#(numeric type n);
   module mkDataLFSR#(Integer i)(LFSR#(Bit#(n)));
endtypeclass

typedef Bit#(32) Seed;
typedef 46 SEEDS;  // Number of seeds available

instance DataLFSR#(32);
   module mkDataLFSR#(Integer i)(LFSR#(Bit#(32)));
      Vector#(SEEDS, Seed) seeds = ?;
      let _ifc <- mkFeedLFSR(seeds[i]);
      return _ifc;
   endmodule
endinstance

instance DataLFSR#(n)
   provisos (Div#(n, 32, q),
	     Mul#(q, 32, n)); // n is a multiple 0f 32

   module mkDataLFSR#(Integer i)(LFSR#(Bit#(n)));
      Vector#(q, LFSR#(Bit#(32))) lfsrs;
      for (Integer j = 0; j<valueof(q); j=j+1)
	 lfsrs[j] <- mkDataLFSR(i+j);

      method Action seed(s);
	 Bit#(n) x = s;
	 for (Integer j = 0; j<valueof(q); j=j+1) begin
	    lfsrs[j].seed(x[31:0]);
	    x = x >> 32;
	 end
      endmethod

      method value();
	 function f(i) = i.value();
	 return pack(map(f, lfsrs));
      endmethod

      method Action next();
	 for (Integer j = 0; j<valueof(q); j=j+1)
	    lfsrs[j].next();
      endmethod
   endmodule
endinstance

typedef struct {
   Bit#(id_size) arid;
   Bit#(id_size) rid;
   Bit#(id_size) bid;
   Bit#(4) arqos;
   Bit#(2) arcache;
   Bit#(1) arlock;
   Bit#(2) arburst;
   Bit#(3) arsize;
   Bit#(length_size) arlen;
   Bit#(length_size) actualLen;
   Bit#(4) region;
   Bit#(2)  response;
   UInt#(4) consecs;
   Int#(4)  dataDelay;
   Bit#(3)  prot;
   UInt#(4) delay;
   Bool     anticipateAValidA;
   Bool     anticipateAValidW;
   Bool     anticipateWValidA;
   Bool     anticipateWValidW;
   Bool     anticipateRespValid;
   Bool     delayAfterResp;
		} AXIparams#(numeric type id_size,
			     numeric type length_size) deriving (Bits, Eq, FShow);

interface RandomsIfc#(type p);
   method Action initialize(UInt#(16) init);
   interface p   randoms;
endinterface

typeclass Randoms#(type p);
   module mkRandoms(RandomsIfc#(p));
endtypeclass

interface AXI4producers#(type a, type b, type c, type d, type e);
   method ActionValue#(Bit#(b))                  address;
   method ActionValue#(Bit#(c))                  data;
   method ActionValue#(Bit#(e))                  auser;
   method ActionValue#(Bit#(e))                  wuser;
   method ActionValue#(Bit#(e))                  buser;
   method ActionValue#(Bit#(TDiv#(c,8)))         strobe;
   method ActionValue#(AXIparams#(a,d)) params;
endinterface

instance Randoms#(AXI4producers#(a,b,c,d,e))
   provisos (NumAlias#(param_size,
		       TMul#(32,TDiv#(SizeOf#(AXIparams#(a,d)),32))),
	     DataLFSR#(param_size));
   module mkRandoms(RandomsIfc#(AXI4producers#(a,b,c,d,e)));
      LFSR#(Bit#(param_size)) paramLFSR <- mkDataLFSR(1);

      return ?;

   endmodule
endinstance

