package Divide;

import BUtils ::*;
import ClientServer ::*;
import FIFO ::*;
import GetPut ::*;

export mkDivider;
export mkSignedDivider;
export mkNonPipelinedDivider;
export mkNonPipelinedSignedDivider;

typedef struct {
   Int#(TAdd#(1,n)) d;
   Int#(TAdd#(2,TAdd#(n,n))) r;
   Int#(TAdd#(1,n)) q;
} DivState#(numeric type n) deriving(Bits, Eq, FShow);

function DivState#(n) operands_to_divstate(Tuple2#(UInt#(m),UInt#(n)) ops)
   provisos(Add#(n, n, m));

   match {.n, .d} = ops;
   return DivState{d: unpack({1'b0,pack(d)}),
                   q: 0,
                   r: unpack({2'b0,pack(n)})
                  };
endfunction

function Bool done(t cmp, t top) provisos(Ord#(t)) = (cmp > top);

function DivState#(n) iterate_divstate(DivState#(n) f, indexT start_index, Integer s)
   provisos(Add#(n, n, m),
   Alias#(UInt#(TAdd#(TLog#(n),1)), indexT));

   Int#(TAdd#(2,m)) bigd = unpack(zExtendLSB(pack(f.d)));
   for (indexT i = 0; i < fromInteger(s); i = i + 1) begin
      indexT index = start_index + i;
      if (!done(index, fromInteger(valueOf(n)))) begin
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
   return f;
endfunction


function Tuple2#(UInt#(n),UInt#(n)) divstate_to_returns(DivState#(n) f);
   f.q = f.q + (-(~f.q));
   if (f.r < 0) begin
      f.q = f.q - 1;
      f.r = f.r + cExtendLSB(f.d);
   end
   UInt#(TAdd#(1,n)) qq = unpack(pack(f.q));
   UInt#(TAdd#(1,n)) rr = cExtendLSB(f.r);
   return tuple2(truncate(qq),truncate(rr));
endfunction

module mkSignedDivider_Core#(
      Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) div,
      FIFO#(Tuple2#(Bool,Bool)) fSign)
      (Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(Add#(n, n, m));

   interface Put request;
      method Action put(Tuple2#(Int#(m),Int#(n)) x);
         match {.a, .b} = x;
         UInt#(m) au = unpack(pack(abs(a)));
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

// non-restoring divider
// n+3 cycle latency, 1 divide per cycle throughput
module mkDivider#(Integer s)(Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))))
   provisos(Add#(n, n, m));

   FIFO#(Tuple2#(UInt#(m),UInt#(n))) fRequest <- mkLFIFO;
   FIFO#(Tuple2#(UInt#(n),UInt#(n))) fResponse <- mkLFIFO;
   FIFO#(DivState#(n)) fFirst <- mkLFIFO;

   rule start;
      fFirst.enq(operands_to_divstate(fRequest.first));
      fRequest.deq;
   endrule

   FIFO#(DivState#(n)) fThis = fFirst;
   FIFO#(DivState#(n)) fNext;

   for (Integer i = 0; !done(i, valueOf(n)); i = i + s) begin
      fNext <- mkLFIFO;
      rule work;
         DivState#(n) f <- toGet(fThis).get;
         fNext.enq(iterate_divstate(f, fromInteger(i), s));
      endrule
      fThis = fNext;
   end

   rule finish;
      DivState#(n) f <- toGet(fThis).get;
      fResponse.enq(divstate_to_returns(f));
   endrule

   interface request = toPut(fRequest);
   interface response = toGet(fResponse);

endmodule

module mkSignedDivider#(Integer s)(Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(Add#(n, n, m));
   Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) div <- mkDivider(s);
   function Integer div_ceil(Integer x, Integer y) = ((x/y) + ((mod(x,y)==0)?0:1));
   FIFO#(Tuple2#(Bool,Bool)) fSign <- mkSizedFIFO(div_ceil(valueOf(n),s) + 2);
   Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))) sdiv <- mkSignedDivider_Core(div, fSign);
   return sdiv;
endmodule

// non-restoring divider
// n+3 cycle latency
module mkNonPipelinedDivider#(Integer s)(Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))))
   provisos(Add#(n, n, m),
            Alias#(UInt#(TAdd#(TLog#(n),1)), indexT));

   Reg#(DivState#(n)) rg_f <- mkRegU;
   Array#(Reg#(Bool)) crg_busy <- mkCReg(2, False);
   Reg#(indexT) rg_index <- mkReg(0);
   Reg#(Bool) rg_done <- mkReg(False);

   rule work (!rg_done);
      rg_f <= iterate_divstate(rg_f, rg_index, s);
      indexT new_index = rg_index + fromInteger(s);
      rg_done <= done(new_index, fromInteger(valueOf(n)));
      rg_index <= new_index;
   endrule

   interface Put request;
      method Action put(Tuple2#(UInt#(m),UInt#(n)) x) if (!crg_busy[1] && rg_done);
         rg_f <= operands_to_divstate(x);
         rg_index <= 0;
         crg_busy[1] <= True;
         rg_done <= False;
      endmethod
   endinterface
   interface Get response;
      method ActionValue#(Tuple2#(UInt#(n),UInt#(n))) get if (crg_busy[0] && rg_done);
         crg_busy[0] <= False;
         return(divstate_to_returns(rg_f));
      endmethod
   endinterface
endmodule

module mkNonPipelinedSignedDivider#(Integer s)(Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(Add#(n, n, m));
   Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) div <- mkNonPipelinedDivider(s);
   FIFO#(Tuple2#(Bool,Bool)) fSign <- mkLFIFO;
   Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))) sdiv <- mkSignedDivider_Core(div, fSign);
   return sdiv;
endmodule

endpackage
