import StmtFSM::*;

interface Bug898_2;
  method Action start();
  method Bool rule_ran();
endinterface

(* synthesize, always_ready, descending_urgency="display3, display" *)
module mkBug898_2(Bug898_2);

  Reg#(Bool) toggle <- mkReg(False);

  rule do_toggle;
   toggle <= !toggle;
  endrule

  PulseWire a <- mkPulseWire;
  PulseWire b <- mkPulseWire;
  PulseWire c <- mkPulseWire; 

  Reg#(Bit#(16)) counter <- mkReg(0);

  rule display(a);
    counter <= counter + 1;
    $display("Pulse b sent at %0t", $time);
    b.send();
  endrule

  rule display2(b);
    $display("Pulse c sent at time %0t", $time);
    c.send();
  endrule 

  rule display3(toggle);
    counter <= counter + 2;
    $display("Counter incremented by 2 at time %0t", $time);
    $display("Pulse c: ", c);
  endrule

  method Action start();
    a.send;
  endmethod

  method rule_ran = c;

endmodule

(* synthesize *)
module sysBug898_2(Empty);
 
  Reg#(Bool) ran <- mkReg(False);

  Bug898_2 simple <- mkBug898_2;

  Stmt testStmts = 
   (seq simple.start;
        simple.start;
        simple.start;
        simple.start;
    endseq);

  rule save_ran;
    ran <= simple.rule_ran;
  endrule

  Empty fsm <- mkAutoFSM(testStmts);

endmodule
