import StmtFSM::*;

interface Bug898;
  method Action start();
  method Bool rule_ran();
endinterface

(* synthesize, always_ready *)
module mkBug898(Bug898);

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

  method Action start();
    a.send;
  endmethod

  method rule_ran = c;

endmodule

(* synthesize *)
module sysBug898(Empty);
 
  Reg#(Bool) ran <- mkReg(False);

  Bug898 simple <- mkBug898;

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
