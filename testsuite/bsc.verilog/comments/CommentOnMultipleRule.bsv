
(* synthesize *)
module mkCommentOnMultipleRule();

   Reg#(Bool) b1 <- mkRegU;
   Reg#(Bool) x1 <- mkRegU;

   Reg#(Bool) b2 <- mkRegU;
   Reg#(Bool) x2 <- mkRegU;

   (* doc = "This rule is important" *)
   rule do_something (b1);
      x1 <= !x1;
   endrule

   (* doc = "This rule is also important" *)
   rule do_another_thing (b2);
      x2 <= !x2;
   endrule

endmodule

