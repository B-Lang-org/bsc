(* synthesize *)
module sysReflexiveDescendingUrgency (Empty);

  Reg#(Bool) r1 <- mkRegU;

  (* descending_urgency = "a, a" *)
  rule a ;
     r1 <= True;
  endrule

endmodule
