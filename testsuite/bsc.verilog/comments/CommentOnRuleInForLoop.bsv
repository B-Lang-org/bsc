
(* synthesize *)
module mkCommentOnRuleInForLoop();

   Reg#(Bool) b[3];
   Reg#(Bool) x[3];

   for (Integer i=0; i<3; i=i+1) begin
      b[i] <- mkRegU;
      x[i] <- mkRegU;
      let bval = b[i], xval = x[i];
      (* doc = "This rule is important" *)
      rule do_something (bval);
	 (x[i]) <= !xval;
      endrule
   end

endmodule

