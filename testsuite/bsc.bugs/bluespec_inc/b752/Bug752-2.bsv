// a -> b <- f -> g
// ^    |    ^    |
// |    v    |    v
// d <- c -> e <- h

(* synthesize *)
module mkBug752_2 (Empty);

  Reg#(Bool) r1 <- mkRegU;
  Reg#(Bool) r2 <- mkRegU;

  (*
   descending_urgency = "a, b",
   descending_urgency = "b, c",
   descending_urgency = "c, d",
   descending_urgency = "d, a",

   descending_urgency = "f, b",
   descending_urgency = "c, e",

   descending_urgency = "e, f",
   descending_urgency = "f, g",
   descending_urgency = "g, h",
   descending_urgency = "h, e"
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

  rule f ;
     r1 <= r2;
     r2 <= r1;
  endrule

  rule g ;
     r1 <= r2;
     r2 <= r1;
  endrule

  rule h ;
     r1 <= r2;
     r2 <= r1;
  endrule

endmodule
