interface Test;
   method Bool ml;
   method Action m2;
   method Bool ok;
endinterface

(* synthesize *)
module mkErrs#(Clock c1, Clock c2, Clock c3)(Test);

  Reg#(Bool) r0 <- mkRegU;
  Reg#(Bool) r1 <- mkRegU(clocked_by c1);
  Reg#(Bool) r2 <- mkRegU(clocked_by c2);
  Reg#(Bool) r3 <- mkRegU(clocked_by c3);

  rule err1(r0);
    r1 <= True;
  endrule
 
  rule err2(r2);
    if(r3) $display("clock-domain crossing");
  endrule

  rule ok_rule(r0);
    $display("Single-clock domain case");
  endrule

  method m1 = r1 && r2;

  method Action m2 if(r3);
    r2 <= !r1;
  endmethod

  method Bool ok = r3;

endmodule