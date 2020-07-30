interface MethodPulse;
  method Action pulse();
endinterface

(* synthesize *)
module mkMethodPulse(MethodPulse);
  
  PulseWire a <- mkPulseWire;

  rule test;
    $display("Pulse sent: %0b", a);
    if(!a) $finish(0);
  endrule

  method Action pulse();
    a.send;
  endmethod

endmodule

(* synthesize *)
module sysMethodPulse(Empty);

  Reg#(Bool) toggle <- mkReg(False);
  Reg#(Bool) done <- mkReg(False);
  MethodPulse test <- mkMethodPulse;

  // failsave exit so C doesn't crash
  rule exit(done);
    $finish(0);
  endrule

  rule step1(!toggle && !done);
    test.pulse;
    toggle <= True;
  endrule

  rule step2(toggle && !done);
    done <= True;
  endrule

endmodule



      
