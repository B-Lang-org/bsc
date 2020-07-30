import FIFO::*;

module mkTurboFIFO(FIFO#(a)) provisos(Bits#(a,sa));

  Reg#(Bool) empty <- mkReg(True);
  Reg#(a)    data <- mkRegU;
  
  PulseWire  do_deq <- mkPulseWire;
  PulseWire  do_enq <- mkPulseWire;

  RWire#(a) bypass_enq <- mkRWire;

  let has_space = empty || do_deq;
  let has_data  = isValid(bypass_enq.wget) || !empty;

  rule write_data(bypass_enq.wget matches tagged Valid .v);
     data <= v;
  endrule

  rule empty_fifo(do_deq && !do_enq);
    empty <= True;
  endrule

  rule fill_fifo(do_enq && !do_deq);
    empty <= False;
  endrule

  method Action enq(v) if (has_space);
    do_enq.send;
    splitIf(!empty,
    action
      data <= v;
    endaction,
    action
      bypass_enq.wset(v);
    endaction);
  endmethod

  method Action deq() if (has_data);
      do_deq.send; 
  endmethod

  method Action clear();
    empty <= True;
  endmethod

  method first() if(has_data);
    if(empty)
      return(fromMaybe(data, bypass_enq.wget));
    else 
      return(data);
  endmethod

endmodule
    
      