import FIFO::*;
import GetPut::*;

interface Ifc#(type t);
  interface Put#(t) in;
  interface Get#(t) out;
endinterface

(* synthesize *)
(* enabled_when_ready = "out.get" *)
module mkGetPutTest(Ifc#(UInt#(8)));
   let m <- wrapFIFO();
   
   interface Put in;
      method Action put(UInt#(8) x);
	 $display("put(%0d)", x);
	 m.in.put(x);
      endmethod
   endinterface
   
   interface Get out;
      method ActionValue#(UInt#(8)) get();
	 let x <- m.out.get();
	 $display("get() -> %0d", x);
	 return x;
      endmethod
   endinterface
endmodule

module wrapFIFO(Ifc#(t)) provisos (Bits#(t,_));
   FIFO#(t) f <- mkFIFO;   
   interface Put in  = fifoToPut(f);
   interface Get out = fifoToGet(f);
endmodule
