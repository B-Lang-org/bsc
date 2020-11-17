package Divide;

import BUtils ::*;
import ClientServer ::*;
import FIFO ::*;
import FIFOF ::*;
import GetPut ::*;
import StmtFSM ::*;

export mkDivider;
export mkSignedDivider;
export mkNonPipelinedDivider;
export mkNonPipelinedSignedDivider;

// non-restoring divider
// n+3 cycle latency, 1 divide per cycle throughput
module mkDivider#(Integer s)(Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))))
   provisos(
      Mul#(2, n, m),
      // per request of bsc
      Add#(b__, n, m),
      Add#(1, m, TAdd#(n, a__))
      );

   FIFO#(Tuple2#(UInt#(m),UInt#(n))) fRequest <- mkLFIFO;
   FIFO#(Tuple2#(UInt#(n),UInt#(n))) fResponse <- mkLFIFO;

   FIFO#(Tuple3#(Int#(TAdd#(1,n)),Int#(TAdd#(1,n)),Int#(TAdd#(2,m)))) fFirst <- mkLFIFO;

   rule start;
      match {.n_, .d_} <- toGet(fRequest).get;
      Int#(TAdd#(1,n)) d = cExtend(d_);
      Int#(TAdd#(2,m)) r = cExtend(n_);
      Int#(TAdd#(1,n)) q = 0;
      fFirst.enq(tuple3(d,q,r));
   endrule

   FIFO#(Tuple3#(Int#(TAdd#(1,n)),Int#(TAdd#(1,n)),Int#(TAdd#(2,m)))) fThis = fFirst;
   FIFO#(Tuple3#(Int#(TAdd#(1,n)),Int#(TAdd#(1,n)),Int#(TAdd#(2,m)))) fNext;

   for (Integer i = 0; i < (valueOf(n)/s+1); i = i + 1) begin
      fNext <- mkLFIFO;
      rule work;
	 //match {.d, .q, .r} <- toGet(fThis).get;
	 let x <- toGet(fThis).get;
	 Int#(TAdd#(1,n)) d = tpl_1(x);
	 Int#(TAdd#(1,n)) q = tpl_2(x);
	 Int#(TAdd#(2,m)) r = tpl_3(x);
	 Int#(TAdd#(2,m)) bigd = cExtendLSB(d);

	 for (Integer j = 0; j < s; j = j + 1) begin
	    if ((i + j) <= valueOf(n)) begin
	       if (r >= 0) begin
		  q = (q << 1) | 1;
		  r = (r << 1) - bigd;
	       end
	       else begin
		  q = (q << 1);
		  r = (r << 1) + bigd;
	       end
	    end
	 end

	 fNext.enq(tuple3(d,q,r));
      endrule
      fThis = fNext;
   end

   rule finish;
      match {.d, .q, .r} <- toGet(fThis).get;

      q = q + (-(~q));
      if (r < 0) begin
	 q = q - 1;
	 r = r + cExtendLSB(d);
      end
      UInt#(TAdd#(1,n)) qq = unpack(pack(q));
      UInt#(TAdd#(1,n)) rr = cExtendLSB(r);
      fResponse.enq(tuple2(truncate(qq),truncate(rr)));
   endrule

   interface request = toPut(fRequest);
   interface response = toGet(fResponse);

endmodule

module mkSignedDivider#(Integer s)(Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(
      Mul#(2, n, m),
      // per request of bsc
      Add#(a__, n, m),
      Add#(1, m, TAdd#(n, b__))
      );

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

module mkNonPipelinedDivider#(Integer s)(Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))))
   provisos(
      Mul#(2, n, m),
      // per request of bsc
      Add#(b__, n, m),
      Add#(1, m, TAdd#(n, a__))
      );

   Reg#(Int#(TAdd#(1,n))) rg_d <- mkRegU;
   Reg#(Int#(TAdd#(1,n))) rg_q <- mkRegU;
   Reg#(Int#(TAdd#(2,m))) rg_r <- mkRegU;

   Array#(Reg#(Bool)) crg_done <- mkCReg(2, False);
   Reg#(Bool) rg_busy <- mkReg(False);
   //Reg#(UInt#(TLog#(TAdd#(TDiv#(n,s),1)))) rg_index <- mkRegU;
   Reg#(UInt#(TLog#(TAdd#(n,1)))) rg_index <- mkRegU;

   rule work(rg_busy);
      Int#(TAdd#(1,n)) d = rg_d;
      Int#(TAdd#(1,n)) q = rg_q;
      Int#(TAdd#(2,m)) r = rg_r;
      Int#(TAdd#(2,m)) bigd = cExtendLSB(d);

      for (Integer j = 0; j < s; j = j + 1) begin
	 if ((rg_index + fromInteger(j)) <= fromInteger(valueOf(n))) begin
	    if (r >= 0) begin
	       q = (q << 1) | 1;
	       r = (r << 1) - bigd;
	    end
	    else begin
	       q = (q << 1);
	       r = (r << 1) + bigd;
	    end
	 end
      end

      if (rg_index == fromInteger(valueOf(n) / s)) begin
	 rg_busy <= False;
	 crg_done[1] <= True;
      end

      rg_index <= rg_index + 1;
      rg_d <= d;
      rg_q <= q;
      rg_r <= r;
   endrule

   interface Put request;
      method Action put(Tuple2#(UInt#(m),UInt#(n)) x) if (!rg_busy);
	 Int#(TAdd#(1,n)) d = cExtend(tpl_2(x));
	 Int#(TAdd#(2,m)) r = cExtend(tpl_1(x));
	 Int#(TAdd#(1,n)) q = 0;

	 rg_busy <= True;
	 crg_done[1] <= False;
	 rg_index <= 0;
	 rg_d <= d;
	 rg_q <= q;
	 rg_r <= r;
      endmethod
   endinterface

   interface Get response;
      method ActionValue#(Tuple2#(UInt#(n),UInt#(n))) get if (crg_done[0]);
	 let d = rg_d;
	 let q = rg_q;
	 let r = rg_r;

	 q = q + (-(~q));
	 if (r < 0) begin
	    q = q - 1;
	    r = r + cExtendLSB(d);
	 end
	 UInt#(TAdd#(1,n)) qq = unpack(pack(q));
	 UInt#(TAdd#(1,n)) rr = cExtendLSB(r);

	 crg_done[0] <= False;
	 return(tuple2(truncate(qq),truncate(rr)));
      endmethod
   endinterface

endmodule

module mkNonPipelinedSignedDivider#(Integer s)(Server#(Tuple2#(Int#(m),Int#(n)),Tuple2#(Int#(n),Int#(n))))
   provisos(
      Mul#(2, n, m),
      // per request of bsc
      Add#(a__, n, m),
      Add#(1, m, TAdd#(n, b__))
      );

   Server#(Tuple2#(UInt#(m),UInt#(n)),Tuple2#(UInt#(n),UInt#(n))) div <- mkNonPipelinedDivider(s);

   Reg#(Bool) rg_asign <- mkRegU;
   Reg#(Bool) rg_bsign <- mkRegU;

   interface Put request;
      method Action put(Tuple2#(Int#(m),Int#(n)) x);
	 match {.a, .b} = x;

	 UInt#(m) au = unpack(pack(abs(a)));
	 UInt#(n) bu = unpack(pack(abs(b)));
	 Bool asign = (signum(a) != extend(signum(b)));
	 Bool bsign = (signum(a) == -1);

	 div.request.put(tuple2(au,bu));

	 rg_asign <= asign;
	 rg_bsign <= bsign;
      endmethod
   endinterface

   interface Get response;
      method ActionValue#(Tuple2#(Int#(n),Int#(n))) get;
	 match {.au, .bu} <- div.response.get;

	 Int#(n) a = unpack(pack(au));
	 Int#(n) b = unpack(pack(bu));

	 a = rg_asign ? -a : a;
	 b = rg_bsign ? -b : b;

	 return(tuple2(a,b));
      endmethod
   endinterface

endmodule

typedef 11 MBits;
typedef 22 NBits;

module mkTb(Empty);
   //FIFOF#(Tuple4#(UInt#(64),UInt#(32),UInt#(32),UInt#(32))) fCheck <- mkLFIFOF;
   Server#(Tuple2#(UInt#(NBits),UInt#(MBits)),Tuple2#(UInt#(MBits),UInt#(MBits))) div <- mkDivider(1);
   FIFOF#(Tuple4#(UInt#(NBits),UInt#(MBits),UInt#(MBits),UInt#(MBits))) fCheck <- mkLFIFOF;

   Server#(Tuple2#(Int#(NBits),Int#(MBits)),Tuple2#(Int#(MBits),Int#(MBits))) sdiv <- mkSignedDivider(1);
   FIFOF#(Tuple4#(Int#(NBits),Int#(MBits),Int#(MBits),Int#(MBits))) fCheck_sdiv <- mkLFIFOF;

   function Action testDividePipe(Integer n, Integer d);
      action
	 UInt#(NBits) ni = fromInteger(n);
	 UInt#(MBits) di = fromInteger(d);
	 UInt#(MBits) q = fromInteger(quot(n,d));
	 UInt#(MBits) p = fromInteger(rem(n,d));
	 div.request.put(tuple2(ni,di));
	 fCheck.enq(tuple4(ni,di,q,p));
      endaction
   endfunction

   function Action testSignedDividePipe(Integer n, Integer d);
      action
	 Int#(NBits) ni = fromInteger(n);
	 Int#(MBits) di = fromInteger(d);
	 Int#(MBits) q = fromInteger(quot(n,d));
	 Int#(MBits) p = fromInteger(rem(n,d));
	 sdiv.request.put(tuple2(ni,di));
	 fCheck_sdiv.enq(tuple4(ni,di,q,p));
      endaction
   endfunction

   Stmt test =
   seq
      testDividePipe(1,2);
      testDividePipe(100,2);
      testDividePipe(100,3);
      testDividePipe(128,5);
      //testDividePipe(219873982173,123812123);
      //testDividePipe('hfff_ffff_ffff_ffff,'hfedc_ba98);
      //testDividePipe(213,'hffff_ffff);
      testDividePipe(2022400,1578);

      testSignedDividePipe(128,5);
      testSignedDividePipe(128,-5);
      testSignedDividePipe(-128,5);
      testSignedDividePipe(-128,-5);

      while (fCheck.notEmpty || fCheck_sdiv.notEmpty)
	 noAction;
   endseq;

   rule check;
      match {.n, .d, .q, .p} <- toGet(fCheck).get;
      match {.qq, .pp} <- div.response.get;

      if (q != qq) begin
	 $display("quot(%d,%d) = %d (expected %d)", n, d, qq, q);
      end

      if (p != pp) begin
	 $display("rem(%d,%d) = %d (expected %d)", n, d, pp, p);
      end
   endrule

   rule check_sdiv;
      match {.n, .d, .q, .p} <- toGet(fCheck_sdiv).get;
      match {.qq, .pp} <- sdiv.response.get;

      if (q != qq) begin
	 $display("quot(%d,%d) = %d (expected %d)", n, d, qq, q);
      end

      if (p != pp) begin
	 $display("rem(%d,%d) = %d (expected %d)", n, d, pp, p);
      end
   endrule

   mkAutoFSM(test);

endmodule

endpackage
