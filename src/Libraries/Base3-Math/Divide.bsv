package Divide;

import BUtils ::*;
import ClientServer ::*;
import FIFO ::*;
import FIFOF ::*;
import GetPut ::*;
import StmtFSM ::*;
import Vector ::*;
import Randomizable ::*;

export mkDivider;
export mkSignedDivider;
export mkNonPipelinedDivider;
export mkNonPipelinedSignedDivider;

typedef struct {
   Int#(TAdd#(1,n)) d;
   Int#(TAdd#(2,TAdd#(n,n))) r;
   Int#(TAdd#(1,n)) q;
} DivState#(numeric type n) deriving(Bits, Eq, FShow);

// non-restoring divider
// n+3 cycle latency, 1 divide per cycle throughput
module mkDivider#(Integer s)(Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))))
   provisos(Add#(n, n, m));

   FIFO#(Tuple2#(UInt#(m),UInt#(n))) fRequest <- mkLFIFO;
   FIFO#(Tuple2#(UInt#(n),UInt#(n))) fResponse <- mkLFIFO;
   FIFO#(DivState#(n)) fFirst <- mkLFIFO;

   function Bool done(Integer cmp) = (cmp > fromInteger(valueOf(n)));

   rule start;
      match {.n, .d} <- toGet(fRequest).get;
      fFirst.enq(DivState{d: unpack({1'b0,pack(d)}),
                          q: 0,
                          r: unpack({2'b0,pack(n)})
                         });
   endrule

   FIFO#(DivState#(n)) fThis = fFirst;
   FIFO#(DivState#(n)) fNext;

   for (Integer i = 0; !done(i); i = i + fromInteger(s)) begin
      fNext <- mkLFIFO;
      rule work;
         DivState#(n) f <- toGet(fThis).get;
         Int#(TAdd#(2,TAdd#(n,n))) bigd = unpack(zExtendLSB(pack(f.d)));
         for (Integer count = i; count < (i+s); count = count + 1) begin
            if (!done(count)) begin
               if (f.r >= 0) begin
                  f.q = (f.q << 1) | 1;
                  f.r = (f.r << 1) - bigd;
               end
               else begin
                  f.q = (f.q << 1);
                  f.r = (f.r << 1) + bigd;
               end
            end
         end
         fNext.enq(f);
      endrule
      fThis = fNext;
   end

   rule finish;
      DivState#(n) f <- toGet(fThis).get;

      f.q = f.q + (-(~f.q));
      if (f.r < 0) begin
         f.q = f.q - 1;
         f.r = f.r + cExtendLSB(f.d);
      end
      UInt#(TAdd#(1,n)) qq = unpack(pack(f.q));
      UInt#(TAdd#(1,n)) rr = cExtendLSB(f.r);
      fResponse.enq(tuple2(truncate(qq),truncate(rr)));
   endrule

   interface request = toPut(fRequest);
   interface response = toGet(fResponse);

endmodule

module mkSignedDivider#(Integer s)(Server#(Tuple2#(Int#(TAdd#(n,n)),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(Add#(n, n, m));

   FIFO#(Tuple2#(Int#(m),Int#(n))) fRequest <- mkLFIFO;
   FIFO#(Tuple2#(Int#(n),Int#(n))) fResponse <- mkLFIFO;

   Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) div <- mkDivider(s);
   FIFO#(Tuple2#(Bool,Bool)) fSign <- mkLFIFO;

   rule start;
      match {.a, .b} <- toGet(fRequest).get;

      UInt#(m) au = unpack(pack(abs(a)));
      UInt#(n) bu = unpack(pack(abs(b)));
      Bool asign = (signum(a) != extend(signum(b)));
      Bool bsign = (signum(a) == -1);

      div.request.put(tuple2(au,bu));
      fSign.enq(tuple2(asign,bsign));
   endrule

   rule finish;
      match {.au, .bu} <- div.response.get;
      match {.asign, .bsign} <- toGet(fSign).get;

      Int#(n) a = unpack(pack(au));
      Int#(n) b = unpack(pack(bu));

      a = asign ? -a : a;
      b = bsign ? -b : b;

      fResponse.enq(tuple2(a,b));
   endrule

   interface request = toPut(fRequest);
   interface response = toGet(fResponse);

endmodule

// non-restoring divider
// n+3 cycle latency
module mkNonPipelinedDivider#(Integer s)(Server#(Tuple2#(UInt#(TAdd#(n,n)),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))))
   provisos(Add#(n, n, m), Alias#(UInt#(TAdd#(TLog#(n),1)), countT));

   Reg#(DivState#(n)) fReg <- mkRegU;
   Reg#(Bool) rg_busy <- mkReg(False);
   Reg#(countT) rg_count <- mkReg(0);

   function Bool done(countT cmp) = (cmp > fromInteger(valueOf(n)));
   Bool div_done = done(rg_count);

   rule work (!div_done);
      DivState#(n) f = fReg;
      Int#(TAdd#(2,TAdd#(n,n))) bigd = unpack(zExtendLSB(pack(f.d)));
      countT count = rg_count;
      for (Integer j = 0; j < s; j = j + 1) begin
         if (!done(count)) begin
            if (f.r >= 0) begin
               f.q = (f.q << 1) | 1;
               f.r = (f.r << 1) - bigd;
            end
            else begin
               f.q = (f.q << 1);
               f.r = (f.r << 1) + bigd;
            end
         end
         count = count + 1;
      end
      fReg <= f;
      rg_count <= count;
   endrule

   interface Put request;
      method Action put(Tuple2#(UInt#(m),UInt#(n)) x) if (!rg_busy);
         match {.num, .den} = x;
         fReg <= DivState{d: unpack({1'b0,pack(den)}),
                          q: 0,
                          r: unpack({2'b0,pack(num)})
                         };
         rg_count <= 0;
         rg_busy <= True;
      endmethod
   endinterface
   interface Get response;
      method ActionValue#(Tuple2#(UInt#(n),UInt#(n))) get if (rg_busy && div_done);
         DivState#(n) f = fReg;
         f.q = f.q + (-(~f.q));
         if (f.r < 0) begin
            f.q = f.q - 1;
            f.r = f.r + unpack(zExtendLSB(pack(f.d)));
         end
         UInt#(TAdd#(1,n)) qq = unpack(pack(f.q));
         UInt#(TAdd#(1,n)) rr = unpack(truncateLSB(pack(f.r)));
         rg_busy <= False;
         return(tuple2(truncate(qq),truncate(rr)));
      endmethod
   endinterface
endmodule

module mkNonPipelinedSignedDivider#(Integer s)(Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(Add#(n, n, m));

   Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) div <- mkNonPipelinedDivider(s);
   FIFO#(Tuple2#(Bool,Bool)) fSign <- mkFIFO;

   interface Put request;
      method Action put(Tuple2#(Int#(m),Int#(n)) x);
         match {.a, .b} = x;
         UInt#(TAdd#(n,n)) au = unpack(pack(abs(a)));
         UInt#(n) bu = unpack(pack(abs(b)));
         div.request.put(tuple2(au,bu));

         Bool asign = msb(a) != msb(b);
         Bool bsign = msb(a) == 1;
         fSign.enq(tuple2(asign,bsign));
      endmethod
   endinterface

   interface Get response;
      method ActionValue#(Tuple2#(Int#(n),Int#(n))) get;
         match {.au, .bu} <- div.response.get;
         match {.asign, .bsign} <- toGet(fSign).get;

         Int#(n) a = unpack(pack(au));
         Int#(n) b = unpack(pack(bu));

         a = asign ? -a : a;
         b = bsign ? -b : b;

         return(tuple2(a,b));
      endmethod
   endinterface
endmodule

endpackage
