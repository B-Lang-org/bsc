(* synthesize *)
module sysRuleBetweenMethods_MEWithFFEdges();

  Reg#(Bool) b <- mkRegU;

  SBRSub sub <- mkRuleBetweenMethods_MEWithFFEdges_Sub;

  PulseWire a_called <- mkPulseWire;
  PulseWire b_called <- mkPulseWire;

  rule call_a(b);
    $display("a");
    sub.a;
    a_called.send;
  endrule

  rule print_a_called(a_called);
     $display("a_called");
  endrule

  rule call_b(!b);
    $display("b");
    sub.b;
    b_called.send;
  endrule
 
  rule print_b_called(b_called);
    $display("b_called");
  endrule

endmodule

interface SBRSub;
  method Action a;
  method Action b;
endinterface

(* synthesize *)
module mkRuleBetweenMethods_MEWithFFEdges_Sub(SBRSub);

  Reg#(Bool) one <- mkRegU;
  Reg#(Bool) two <- mkRegU;
  Reg#(Bool) three <- mkRegU;

  rule middle;
     two <= one;
     three <= two;
  endrule

  method Action a;
     three <= !three;
  endmethod

  method Action b;
     one <= True;
  endmethod

endmodule

