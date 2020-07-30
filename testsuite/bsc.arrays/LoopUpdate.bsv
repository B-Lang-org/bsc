import Vector::*;

typedef 200 Max_index;

Integer max_index = valueof(Max_index);

(* synthesize *)
module sysLoopUpdate(Empty);

  Reg#(Vector#(Max_index, Bool)) scoreboard <- mkReg(replicate(False));

  Reg#(Bit#(32)) index <- mkReg(0);

  rule count_index;
    index <= index + 1;
  endrule

  function a primNoRead(a x) = x;

  rule set_bit;
    scoreboard[index] <= True;
  endrule

  rule display_scoreboard;
    $display("Scoreboard: %h index: %0d", scoreboard, index);
    if(index == fromInteger(max_index)) $finish(0);
  endrule

endmodule
