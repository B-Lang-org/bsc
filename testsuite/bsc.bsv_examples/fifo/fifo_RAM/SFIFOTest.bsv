import SFIFOSupport::*;
import RAM :: *;

// For mkDummyRAM
import ClientServer :: *;
import GetPut :: *;
import RegFile :: *;
import FIFO :: *;

module mkSFIFOTest(Empty);

  Reg#(Bool) b();
  mkReg#(False) the_b(b);

  Reg#(Bit#(8)) r();
  mkReg#(0) the_r(r);

  // RAM model with a delay of 3 clocks
  RAM#(Bit#(3),Bit#(4)) mem();
  mkDummyRAM#(3, 3'd0, 3'd7) the_mem(mem);

  SFIFO#(Bit#(4)) f();
  mkSFIFO#(mem, 3'd0, 3'd7) the_f(f);

  rule r1 (!b && !f.isFull);
    Bit#(4) val = truncate(r);
    $display("Enqueuing: %0d", val);
    f.enq(val);
    r <= r + 1;
  endrule

  rule r2 (!b && f.isFull);
    $display("FIFO is full");
    b <= True;
  endrule

  rule r3 (b && !f.isEmpty);
    $display("Dequeuing: %0d", f.first());
    f.deq();
  endrule

  rule r4 (b && f.isEmpty);
    $display("Done");
    $finish(0);
  endrule

endmodule


module mkDummyRAM#(Integer delay, adr lo, adr hi) (RAM#(adr,dta))
  provisos(Bits#(adr,adr_sz), Bits#(dta,dta_sz),
	   Bits#(RAMreq#(adr,dta),req_sz),
	   Bits#(Maybe#(RAMreq#(adr,dta)),mreq_sz)
	   );

  RegFile#(adr,dta) arr();
  mkRegFile#(lo, hi) the_arr(arr);

  Reg#(Maybe#(RAMreq#(adr,dta))) shift_regs[delay];
  // shift_regs <- map(const(mkReg(Invalid)),upto(1,delay))
  Integer i;
  for (i=0; i<delay; i=i+1)
    begin
      Reg#(Maybe#(RAMreq#(adr,dta))) r();
      mkReg#(Invalid) the_r(r);
      shift_regs[i] = asReg(r);
    end

  RWire#(RAMreq#(adr,dta)) req();
  mkRWire the_req(req);

  // maximum number of requests in flight
  Integer max_reqs = delay + 1;

  FIFO#(dta) res_queue();
  mkSizedFIFO#(max_reqs) the_res_queue(res_queue);

  // Keep track of number of gets in flight,
  // in order to apply back pressure when not enough space to store
  // all the results.
  // We have separate in and out credits, so that making requests and
  // handling requests can be SC.
  Reg#(Bit#(32)) in_credits();
  mkReg#(0) the_in_credits(in_credits);

  Reg#(Bit#(32)) out_credits();
  mkReg#(0) the_out_credits(out_credits);

  Bit#(32) max_credits = fromInteger(max_reqs);

  Bool no_more_reqs = ((in_credits - out_credits) == max_credits);

  (* fire_when_enabled *)
  rule shift (True);
    // shift the requests
    Integer i;
    for (i=0; i<delay; i=i+1)
      action
        (shift_regs[i]) <= (i == 0) ? req.wget() : (shift_regs[i-1])._read;
      endaction

    // handle the request
    case ((shift_regs[delay-1])._read) matches
	tagged Invalid: noAction;
        tagged Valid (tagged Read .idx):
	    action
	      out_credits <= out_credits + 1;
	      // We know that the FIFO won't be full
	      res_queue.enq(arr.sub(idx));
	    endaction
        tagged Valid (tagged Write {.idx, .val}):
            action
	      arr.upd(idx,val);
	    endaction
    endcase
  endrule

  interface Put request;
     method put(RAMreq#(adr,dta) in_req) if (!no_more_reqs);
	action
	   req.wset(in_req);
        endaction
     endmethod
  endinterface

  interface Get response;
     method get();  // if res_queue is not empty
	actionvalue
	   in_credits <= in_credits + 1;
	   // We know that the FIFO won't be empty;
	   res_queue.deq;
	   return res_queue.first;
	endactionvalue
     endmethod
  endinterface

endmodule

