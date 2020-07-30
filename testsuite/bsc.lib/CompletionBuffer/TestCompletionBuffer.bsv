import CompletionBuffer::*;
import FIFO::*;
import ClientServer::*;
import GetPut::*;

(* synthesize *)
module sysTestCompletionBuffer();

   Reg#(Bit#(10)) ticks <- mkReg(0);

   rule cnt ;
      ticks <= ticks + 1;
      if (ticks > 50) $finish(0);
   endrule

   // -----

   Reg#(Bit#(32)) tag <- mkReg(0);

   FIFO#(Bit#(32)) f_req <- mkFIFO;

   rule do_req;
       f_req.enq(tag);
       tag <= tag + 3;
   endrule

   // -----

   CompletionBuffer#(8, Bit#(32)) cb <- mkCompletionBuffer;

   Server#(Tuple2#(CBToken#(8), Bit#(32)),
           Tuple2#(CBToken#(8), Bit#(32))) fs[8];
   for (Integer n=0; n<8; n=n+1) begin
      fs[n] <- mkDelay(fromInteger(n));

      rule do_dispatch;
         let tok <- cb.reserve.get;
         fs[n].request.put(tuple2(tok, f_req.first));
         f_req.deq;
      endrule

      rule do_complete;
         let rsp <- fs[n].response.get;
         cb.complete.put(rsp);
      endrule
   end

   // -----

   rule do_drain;
      let rsp <- cb.drain.get;
      $display("Drain: %d", rsp);
   endrule

endmodule


module mkDelay#(Bit#(8) depth)(Server#(t,t))
  provisos (Bits#(t, szt));

    Reg#(t) r_data <- mkRegU;
    Reg#(Maybe#(Bit#(8))) r_delay <- mkReg(tagged Invalid);

    rule do_delay (r_delay matches tagged Valid .n &&& (n > 0));
       r_delay <= tagged Valid (n-1);
    endrule

    interface Put request;
       method Action put(t data) if (r_delay == tagged Invalid);
          r_data <= data;
          r_delay <= tagged Valid depth;
       endmethod
    endinterface

    interface Get response;
       method ActionValue#(t) get() if (r_delay == tagged Valid 0);
          r_delay <= tagged Invalid;
          return r_data;
       endmethod
    endinterface

endmodule

