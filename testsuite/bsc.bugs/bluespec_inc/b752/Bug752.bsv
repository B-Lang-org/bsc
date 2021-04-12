(* synthesize *)
module mkBug752 (Empty);

  Reg#(Bool) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;

  (*
   descending_urgency = "a, b",
   descending_urgency = "b, c",
   descending_urgency = "c, a",
   descending_urgency = "a, d",
   descending_urgency = "d, e",
   descending_urgency = "e, a"
   *)
  rule a ;
     r1 <= r2;
     r2 <= r1;
  endrule

  rule b ;
     r1 <= r2;
     r2 <= r1;
  endrule

  rule c ;
     r1 <= r2;
     r2 <= r1;
  endrule

  rule d ;
     r1 <= r2;
     r2 <= r1;
  endrule

  rule e ;
     r1 <= r2;
     r2 <= r1;
  endrule

endmodule
