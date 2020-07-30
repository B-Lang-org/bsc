import ConfigReg::*;

interface FindFIFO#(type t);
   method Action enq(t x);
   method Action deq();
   method t      first();
   method Action clear();
   method Bool   find(function Bool f(t x));
   method Bool   notEmpty();
endinterface

module mkFindFIFO (FindFIFO#(t)) provisos (Bits#(t,szt));

   Reg#(Maybe#(t)) data();
   mkReg#(Invalid) data_r(data);

   RWire#(void) deq_probe();
   mkRWire deq_probe_r(deq_probe);

   RWire#(t) enq_probe();
   mkRWire enq_probe_r(enq_probe);

   RWire#(void) clr_probe();
   mkRWire clr_probe_r(clr_probe);

   Bool is_deq = isValid(deq_probe.wget);
   Bool is_enq = isValid(enq_probe.wget);
   Bool is_clr = isValid(clr_probe.wget);
   
   Bool has_data = isValid(data);
   Bool can_enq = is_deq || !has_data;
   Bool can_deq = has_data;

   (* fire_when_enabled, no_implicit_conditions *)
   rule handle_inputs;
/*
      // This doesn't work

      Maybe#(t) new_data = data;
      if (is_deq) begin
	 $display("Dequeing data");
	 new_data = Invalid;
      end
      if (is_enq) begin
	 $display("Enqueing data: %b", enq_probe.wget);
	 new_data = enq_probe.wget;
	 $display("new_data1: %b", new_data);
      end
      $display("new_data2: %b", new_data);
      if (is_clr) begin
	 $display("Clearing FIFO");
	 new_data = Invalid;
      end
      $display("Enq: %b, Deq: %b, Clr: %b",
	       pack(is_enq), pack(is_deq), pack(is_clr));
      $display("data: %b", data);
      $display("new_data3: %b", new_data);
      data <= new_data;
*/
      if (is_clr)
	 data <= Invalid;
      else
	 if (is_enq)
	    data <= enq_probe.wget;
	 else
	    if (is_deq)
	       data <= Invalid;
	    else
	       data <= data;
   endrule
   
   method enq(x) if (can_enq) = enq_probe.wset(x);
   method deq() if (can_deq) = deq_probe.wset(?);
   method clear() = clr_probe.wset(?);
   
   method first() if (has_data) = validValue(data);

   method find(f) = has_data ? f(validValue(data)) : False;
   method notEmpty() = has_data;

endmodule

