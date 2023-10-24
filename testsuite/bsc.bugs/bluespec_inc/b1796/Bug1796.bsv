import FIFO::*;
import FIFOF::*;
import GetPut::*;
import ClientServer::*;
import Vector::*;
import FixedPoint::*;
import Complex::*;
import Counter::*;

// --------------------

(* synthesize *)
module mkPipelinedMultiplierUG_32(PipelinedMultiplier#(3, Bit#(34)));
endmodule

(* synthesize *)
module mkMultiplierFP16DSP (Multiplier#(FixedPoint#(7,10)));
   let m <- mkPipelinedMultiplierFixedPoint(mkDePipelinedMultiplier(mkPipelinedMultiplierG(mkPipelinedMultiplierUG_32)));
   return m;
endmodule

(* synthesize *)
module sysBug1796 (Empty);
   BatchCS#(FixedPoint#(7,10),4)  top <- mkBatchCS(mkMultiplierFP16DSP ); //mkMul);
endmodule

// --------------------

interface PipelinedMultiplier#(numeric type stages, type tnum);
  interface Put#(Tuple2#(tnum, tnum)) request;
  interface Get#(tnum) response;
endinterface

module [m] mkPipelinedMultiplierG(m#(PipelinedMultiplier#(stages, tnum)) mkmul, PipelinedMultiplier#(stages, tnum) ifc)
    provisos(Bits#(tnum, tnum_sz), IsModule#(m, b__)) ;

    PipelinedMultiplier#(stages, tnum) mul <- mkPipelinedMultiplierSG(mkmul);
    FIFOF#(tnum) results <- mkGSizedFIFOF(True, False, valueof(stages) + 1);
    Counter#(TAdd#(1, TLog#(stages))) pending <- mkCounter(0);

    (* fire_when_enabled *)
    rule takeresult (True);
        tnum x <- mul.response.get();
        results.enq(x);
    endrule

    interface Put request;
        method Action put(Tuple2#(tnum, tnum) operands) if (pending.value() != fromInteger(valueof(stages)));
            pending.up();
            mul.request.put(operands);
        endmethod
    endinterface

    interface Get response;
        method ActionValue#(tnum) get();
            pending.down();
            results.deq();
            return results.first();
        endmethod
    endinterface
endmodule

module [m] mkPipelinedMultiplierSG(m#(PipelinedMultiplier#(stages, tnum)) mkmul, PipelinedMultiplier#(stages, tnum) ifc)
    provisos(IsModule#(m, a__));

    PipelinedMultiplier#(stages, tnum) mul <- mkmul();

    PulseWire incoming <- mkPulseWire();
    Vector#(stages, Reg#(Bool)) valids <- replicateM(mkReg(False));

    (* fire_when_enabled *)
    (* no_implicit_conditions *)
    rule shift (True);
        valids[0] <= incoming;
        for (Integer i = 1; i < valueof(stages); i = i+1) begin
            valids[i] <= valids[i-1];
        end
    endrule

    interface Put request;
        method Action put(Tuple2#(tnum, tnum) operands);
            mul.request.put(operands);
            incoming.send();
        endmethod
    endinterface

    interface Get response;
        method ActionValue#(tnum) get() if (valids[valueof(stages)-1]);
            tnum x <- mul.response.get();
            return x;
        endmethod
    endinterface

endmodule

// --------------------

typedef TMul#(TAdd#(7, 10),2) BitLen;

typedef Server#(Tuple2#(tnum, tnum), tnum) Multiplier#(type tnum);

module [m] mkDePipelinedMultiplier(m#(PipelinedMultiplier#(stages, tnum)) mkmul, Multiplier#(tnum) ifc)
    provisos(IsModule#(m, m__));

    PipelinedMultiplier#(stages, tnum) m <- mkmul;
    interface Put request = m.request;
    interface Get response = m.response;
endmodule

module [m] mkPipelinedMultiplierFixedPoint(m#(Multiplier#(Bit#(BitLen))) mkmul, Multiplier#(FixedPoint#(is, fs)) ifc)
    provisos(
      IsModule#(m, m__),
      Add#(a__, TAdd#(is, fs), BitLen),
      Min#(is, 1, 1),
      Min#(TAdd#(is, fs), 2, 2)
    );

    Multiplier#(Bit#(BitLen)) mul <- mkmul;

    FIFO#(Bool) negative <- mkSizedFIFO(4);

    interface Put request;
        method Action put(Tuple2#(FixedPoint#(is, fs), FixedPoint#(is, fs)) x);
            match {.x0, .x1} = x;
            let s_x = fxptGetInt(x0) < 0;
            let s_y = fxptGetInt(x1) < 0;
            let a = s_x ? -x0 : x0;
            let b = s_y ? -x1 : x1;
            mul.request.put(tuple2(zeroExtend(pack(a)), zeroExtend(pack(b))));
            negative.enq((s_x && !s_y) || (!s_x && s_y));
        endmethod
    endinterface

    interface Get response;
        method ActionValue#(FixedPoint#(is, fs)) get();
            Bit#(BitLen) bits <- mul.response.get();
            FixedPoint#(is, fs) rv = unpack(bits[(2*valueof(fs)+valueof(is)-1):valueof(fs)]);
            Bool neg <- toGet(negative).get();
            return (neg ? -rv : rv);
        endmethod
    endinterface
endmodule

// --------------------

interface BatchCS#(type tnum, numeric type tsize);
	method Action put(Vector#(tsize,Complex#(tnum)) invector);
	interface Get#(Vector#(tsize,tnum)) outvec;
endinterface

module [m] mkBatchCS (m#(Multiplier#(tnum)) mkmul, BatchCS#(tnum,tsize) ifc)
	provisos(IsModule#(m,m__), Bits#(tnum, a__),Arith#(tnum));

Vector#(tsize, Multiplier#(tnum)) relP <- replicateM(mkmul());//product of real part
Vector#(tsize, Multiplier#(tnum)) imgP <- replicateM(mkmul());//product of imaginary part

FIFO#(Vector#(tsize,Complex#(tnum))) inputVec <- mkFIFO();
FIFO#(Vector#(tsize,tnum)) outputVec <- mkFIFO();

	rule cloudiblock;

        Vector#(tsize, tnum) outvectop = newVector;
        Vector#(tsize, tnum) outvectop1 = newVector;
        Vector#(tsize, tnum) outvectop2 = newVector;

        for(Integer i =0;i<valueof(tsize);i=i+1) begin
			outvectop1[i] <- relP[i].response.get();
			outvectop2[i] <- imgP[i].response.get();
		end

        for(Integer j =0;j<valueof(tsize);j=j+1) begin
			outvectop[j] = outvectop1[j] + outvectop2[j];
        end

		outputVec.enq(outvectop);

	endrule

//interface Put invec;
	method Action put(invector);
		for(Integer i =0;i<valueof(tsize);i=i+1) begin
			relP[i].request.put(tuple2(invector[i].rel, invector[i].rel));
			imgP[i].request.put(tuple2(invector[i].img, invector[i].img));
		end
	endmethod
//endinterface
interface Get outvec = toGet(outputVec);
endmodule

// --------------------

