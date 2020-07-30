import Vector::*;

typedef 200 Max_index;

Integer max_index = valueof(Max_index);

(* synthesize *)
module sysLoopUpdate2(Empty);

  Reg#(Vector#(Max_index, Bool)) scoreboard <- mkReg(replicate(False));

  Reg#(Bit#(32)) index <- mkReg(0);

  rule count_index;
    index <= index + 1;
  endrule

  rule set_bit;
    Vector#(Max_index, Bool) new_scoreboard = scoreboard;
    for(Integer i = 0; i < max_index; i = i + 1)
    begin
      if(fromInteger(i) == index)
        new_scoreboard[i] = True;
    end
    scoreboard <= new_scoreboard;
  endrule

  rule display_scoreboard;
    $display("Scoreboard: %h index: %0d", scoreboard, index);
    if(index == fromInteger(max_index)) $finish(0);
  endrule

endmodule
