
(* synthesize *)
module mkCommentOnRuleNest();

   Reg#(Bool) b <- mkRegU;
   Reg#(Bool) x <- mkRegU;
   Reg#(Bool) y <- mkRegU;

   (* doc = "This rule is important" *)
   rule will_do (y);

      rule something (b);
	 x <= !x;
      endrule

      (* doc = "This is another thing" *)
      rule another_thing (!b);
	 b <= !b;
      endrule
   endrule

endmodule

