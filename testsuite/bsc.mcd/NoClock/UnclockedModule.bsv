interface CounterIfc;
  method Action next();
  method UInt#(32) value();
endinterface

module mkCounter(CounterIfc);
  Reg#(UInt#(32)) cntr <- mkReg(0);

  method Action next();
    cntr <= cntr + 1;
  endmethod

  method UInt#(32) value();
    return cntr;
  endmethod

endmodule

(* synthesize *)
module sysUnclockedModule();

  CounterIfc counter <- mkCounter(clocked_by(noClock));

  Reg#(UInt#(8)) cycles <- mkReg(0);

  rule r1;
    counter.next();
  endrule

  rule r2;
    $display("counter = %h", counter.value());
  endrule

  rule count_cycles;
    cycles <= cycles + 1;
  endrule

  rule done (cycles == 10);
    $finish(0);
  endrule
  
endmodule
