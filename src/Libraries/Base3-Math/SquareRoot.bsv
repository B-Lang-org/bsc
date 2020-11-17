package SquareRoot;

import BUtils ::*;
import ClientServer ::*;
import FIFO ::*;
import FIFO ::*;
import FIFOF ::*;
import FixedPoint ::*;
import GetPut ::*;
import Real ::*;
import StmtFSM ::*;

export mkSquareRooter;
export mkFixedPointSquareRooter;
export mkNonPipelinedSquareRooter;

module mkSquareRooter#(Integer n)(Server#(UInt#(m),Tuple2#(UInt#(m),Bool)))
   provisos(
      Div#(m, 2, m2),
      // m must be even for this implementation to work
      Mul#(m2, 2, m)
      );

   FIFO#(UInt#(m)) fRequest <- mkLFIFO;
   FIFO#(Tuple2#(UInt#(m),Bool)) fResponse <- mkLFIFO;

   FIFO#(Tuple4#(Maybe#(Bit#(m)),Bit#(m),Bit#(m),Bit#(m))) fFirst <- mkLFIFO;

   rule start;
      let op <- toGet(fRequest).get;
      let s = pack(op);
      Bit#(m) r = 0;
      Bit#(m) b = zExtendLSB(2'b01);

      let s0 = countZerosMSB(s);
      let b0 = countZerosMSB(b);
      if (s0 > 0) begin
	 let shift = (s0 - b0);
	 if ((shift & 1) == 1)
	    shift = shift + 1;
	 b = b >> shift;
      end

      fFirst.enq(tuple4(tagged Invalid,s,r,b));
   endrule

   FIFO#(Tuple4#(Maybe#(Bit#(m)),Bit#(m),Bit#(m),Bit#(m))) fThis = fFirst;
   FIFO#(Tuple4#(Maybe#(Bit#(m)),Bit#(m),Bit#(m),Bit#(m))) fNext;

   for (Integer i = 0; i < valueOf(m2)/n+1; i = i + 1) begin
      fNext <- mkLFIFO;
      rule work;
	 //match {.res, .s, .r, .b} <- toGet(fThis).get;
	 let x <- toGet(fThis).get;
	 Maybe#(Bit#(m)) res = tpl_1(x);
	 Bit#(m) s = tpl_2(x);
	 Bit#(m) r = tpl_3(x);
	 Bit#(m) b = tpl_4(x);

	 for (Integer j = 0; j < n; j = j + 1) begin
	    if ((i + j) <= valueOf(m2)) begin
	       if (res matches tagged Invalid) begin
		  if (b == 0) begin
		     res = tagged Valid r;
		  end
		  else begin
		     let sum = r + b;

		     if (s >= sum) begin
			s = s - sum;
			r = (r >> 1) + b;
		     end
		     else begin
			r = r >> 1;
		     end

		     b = b >> 2;
		  end
	       end
	    end
	 end

	 fNext.enq(tuple4(res,s,r,b));
      endrule
      fThis = fNext;
   end

   rule finish;
      match {.res, .s, .r, .b} <- toGet(fThis).get;

      fResponse.enq(tuple2(unpack(fromMaybe(0,res)),(s != 0)));
   endrule

   interface request = toPut(fRequest);
   interface response = toGet(fResponse);

endmodule

module mkFixedPointSquareRooter#(Integer n)(Server#(FixedPoint#(isize,fsize),Tuple2#(FixedPoint#(isize,fsize),Bool)))
   provisos(
      Add#(isize,fsize,m),
      // m must be even for this implementation to work
      Mul#(TDiv#(m, 2), 2, m),
      Add#(a__, 1, TLog#(TAdd#(1, m)))
      );

   FIFO#(FixedPoint#(isize,fsize)) fRequest <- mkLFIFO;
   FIFO#(Tuple2#(FixedPoint#(isize,fsize),Bool)) fResponse <- mkLFIFO;

   Server#(UInt#(m),Tuple2#(UInt#(m),Bool)) sqrt <- mkSquareRooter(n);
   FIFO#(Int#(TAdd#(TLog#(m),1))) fShift <- mkLFIFO;

   rule start;
      let op <- toGet(fRequest).get;
      UInt#(m) value = unpack({op.i,op.f});

      let zeros = countZerosMSB(pack(value));
      // The decimal place in 'value' is at 'fsize' bit place.
      // After alignment, it is 'zeros + fsize' bit place.
      // After square root, it is '(zeros + fsize) / 2' bit place.
      //
      // The shift restores the decimal to 'fsize' bit place, thus a
      // right (left, if negative) shift by '(zeros + fsize) / 2 -
      // fsize' or '(zeros - fsize) / 2'.
      //
      // Since it is not possible to shift by half a bit, adjust
      // zeros, if necessary, so that shift is an integer.
      Int#(TAdd#(TLog#(m),2)) shift2 = cExtend(zeros) - fromInteger(valueOf(fsize));
      Int#(TAdd#(TLog#(m),1)) shift = cExtendLSB(shift2);
      UInt#(1) lsb = cExtend(shift2);

      // align input
      value = value << (zeros - extend(lsb));

      sqrt.request.put(value);
      fShift.enq(shift);
   endrule

   rule finish;
      match {.result, .inexact} <- sqrt.response.get;
      let shift <- toGet(fShift).get;

      // shift result as necessary
      if (shift >= 0)
         result = result >> shift;
      else  // invert direction if shift is negative
         result = result << (-shift);

      FixedPoint#(isize,fsize) fx;
      fx.i = truncateLSB(pack(result));
      fx.f = truncate(pack(result));

      fResponse.enq(tuple2(fx,inexact));
   endrule

   interface request = toPut(fRequest);
   interface response = toGet(fResponse);

endmodule

module mkNonPipelinedSquareRooter#(Integer n)(Server#(UInt#(m),Tuple2#(UInt#(m),Bool)))
   provisos(
      // per request of bsc
      Add#(a__, 2, m),
      Log#(TAdd#(1, m), TLog#(TAdd#(m, 1)))
      );

   Reg#(Maybe#(Bit#(m))) rg_res <- mkRegU;
   Reg#(Bit#(m)) rg_s <- mkRegU;
   Reg#(Bit#(m)) rg_r <- mkRegU;
   Reg#(Bit#(m)) rg_b <- mkRegU;

   Array#(Reg#(Bool)) crg_done <- mkCReg(2, False);
   Reg#(Bool) rg_busy <- mkReg(False);
   //Reg#(UInt#(TLog#(TAdd#(TDiv#(TDiv#(m,2),n),1)))) rg_index <- mkRegU;
   Reg#(UInt#(TLog#(TAdd#(TDiv#(m,2),1)))) rg_index <- mkRegU;

   rule work(rg_busy);
      Maybe#(Bit#(m)) res = rg_res;
      Bit#(m) s = rg_s;
      Bit#(m) r = rg_r;
      Bit#(m) b = rg_b;

      for (Integer j = 0; j < n; j = j + 1) begin
	 if ((rg_index + fromInteger(j)) <= fromInteger(valueOf(m)/2)) begin
	    if (res matches tagged Invalid) begin
	       if (b == 0) begin
		  res = tagged Valid r;
	       end
	       else begin
		  let sum = r + b;

		  if (s >= sum) begin
		     s = s - sum;
		     r = (r >> 1) + b;
		  end
		  else begin
		     r = r >> 1;
		  end

		  b = b >> 2;
	       end
	    end
	 end
      end

      if (rg_index == fromInteger(valueOf(m) / 2 / n)) begin
	 rg_busy <= False;
	 crg_done[1] <= True;
      end

      rg_index <= rg_index + 1;
      rg_res <= res;
      rg_s <= s;
      rg_r <= r;
      rg_b <= b;
   endrule

   interface Put request;
      method Action put(UInt#(m) x) if (!rg_busy);
	 action
	    let s = pack(x);
	    Bit#(m) r = 0;
	    Bit#(m) b = zExtendLSB(2'b01);

	    let s0 = countZerosMSB(s);
	    let b0 = countZerosMSB(b);
	    if (s0 > 0) begin
	       let shift = (s0 - b0);
	       if ((shift & 1) == 1)
		  shift = shift + 1;
	       b = b >> shift;
	    end

	    rg_busy <= True;
	    crg_done[1] <= False;
	    rg_index <= 0;
	    rg_res <= tagged Invalid;
	    rg_s <= s;
	    rg_r <= r;
	    rg_b <= b;
	 endaction
      endmethod
   endinterface

   interface Get response;
      method ActionValue#(Tuple2#(UInt#(m),Bool)) get if (crg_done[0]);
	 crg_done[0] <= False;
	 return tuple2(unpack(fromMaybe(0,rg_res)),(rg_s != 0));
      endmethod
   endinterface

endmodule

//typedef UInt#(32) SqrtT;
typedef UInt#(64) SqrtT;
typedef FixedPoint#(32,32) SqrtTFx;

module mkTb(Empty);
   Server#(SqrtT,Tuple2#(SqrtT,Bool)) sqrtm <- mkSquareRooter(1);
   Server#(SqrtTFx,Tuple2#(SqrtTFx,Bool)) sqrtfxm <- mkFixedPointSquareRooter(1);
   FIFOF#(Tuple4#(SqrtT,SqrtT,SqrtTFx,SqrtTFx)) fCheck <- mkLFIFOF;

   function Action testSqrtPipe(Real n);
      action
	 SqrtT ni = fromInteger(trunc(n));
	 SqrtT ri = fromInteger(round(sqrt(n)));
	 SqrtTFx nfx = fromReal(n);
	 SqrtTFx rfx = fromReal(sqrt(n));
	 sqrtm.request.put(ni);
	 sqrtfxm.request.put(nfx);
	 fCheck.enq(tuple4(ni,ri,nfx,rfx));
      endaction
   endfunction

   Stmt test =
   seq
      testSqrtPipe(1);
      testSqrtPipe(2);
      testSqrtPipe(4);
      testSqrtPipe(10);
      //testSqrtPipe(123456789);
      testSqrtPipe('h2000000);
      testSqrtPipe('h3d80000);
      testSqrtPipe('h3ef9db0);
      testSqrtPipe('h3ffffff);
      testSqrtPipe('h3ffc000);
      testSqrtPipe('hfffffffe_00000000);
      testSqrtPipe('hf0000000_00000000);
      testSqrtPipe('hffff0000_00000000);
      testSqrtPipe('hfffe0000);

      testSqrtPipe(536870912.9375);
      testSqrtPipe(1073741824.96875);
      testSqrtPipe(0.5);
      testSqrtPipe(0.25);

      while (fCheck.notEmpty)
	 noAction;
   endseq;

   rule check;
      match {.n,.r,.nfx,.rfx} <- toGet(fCheck).get;
      match {.rr, .inexact} <- sqrtm.response.get;
      match {.rrfx, .inexactfx} <- sqrtfxm.response.get;

      if (r != rr) begin
	 $display("sqrt(%d) = %d (expected %d)", n, rr, r);
      end
      else begin
	 $display("sqrt(%d) = %d", n, rr);
      end

      if (rfx != rrfx) begin
	 $display("sqrtfx(", fshow(nfx), ") = ", fshow(rrfx), " (expected ", fshow(rfx) ,")");
      end
      else begin
	 $display("sqrtfx(", fshow(nfx), ") = ", fshow(rrfx));
      end
   endrule

   mkAutoFSM(test);

endmodule

endpackage
