package RandomSynth;

import Control::*;
import FIFO::*;
import LFSR::*;
import Randomizeable::*;
import Vector::*;

module mkGenericRandomizer_Synth (Randomize#(a))
   provisos (Bits#(a, sa), Bounded#(a));

   LFSR#(Bit#(sa)) lfsr <- mkVecLFSR32;

   interface Control cntrl;
      method Action init();
         lfsr.seed(?);
      endmethod
   endinterface

   method ActionValue#(a) next();
      lfsr.next;
      return unpack(truncate(lfsr.value));
   endmethod
endmodule

module mkConstrainedRandomizer_Synth#(a min, a max) (Randomize#(a))
   provisos (Bits#(a, sa), Bounded#(a));

   LFSR#(Bit#(sa)) lfsr <- mkVecLFSR32;

   interface Control cntrl;
      method Action init();
         lfsr.seed(?);
      endmethod
   endinterface

   method ActionValue#(a) next();
      Bit#(sa) candidate = truncate(lfsr.value);
      lfsr.next;
      Bit#(sa) diff = pack(max) - pack(min);
      Bit#(sa) mask = '1 >> countZerosMSB(diff);
      candidate = candidate & mask;
      if (candidate > diff)
	 candidate = candidate - diff;
      candidate = candidate + pack(min);
      return unpack(candidate);
   endmethod
endmodule

module mkVecLFSR32 (LFSR#(Bit#(sz)))
   provisos (Div#(sz,32,n));

   Vector#(n, LFSR#(Bit#(32))) rs <- replicateM(mkLFSR_32);

   method Action seed (Bit#(sz) s);
      let tmp = {32'b0, s};
      Vector#(n,Bit#(32)) seeds = unpack(tmp[(valueOf(n)*32)-1:0]);
      for (Integer i=0; i<valueOf(n); i=i+1)
         // add "i" so there's less chance of chunks having the same seed
         rs[i].seed(seeds[i] + fromInteger(i));
   endmethod
   method Action next ();
      for (Integer i=0; i<valueOf(n); i=i+1)
         rs[i].next;
   endmethod
   method Bit#(sz) value();
      function getVal(r) = r.value;
      let tmp = pack(map(getVal, rs));
      return tmp[valueOf(sz)-1:0];
   endmethod
endmodule

endpackage
