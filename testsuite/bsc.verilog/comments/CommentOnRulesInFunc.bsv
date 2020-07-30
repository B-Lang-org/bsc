
function Rules mkR(Reg#(Bool) b, Reg#(Bool) x, Reg#(Bool) y);
   return ((* doc = "This rule is important" *)
	   rules
	      rule do_something (!y);
		 x <= !x;
	      endrule

	      (* doc = "This is another thing" *)
	      rule do_another_thing (!b);
		 b <= !b;
	      endrule
	   endrules);
endfunction


(* synthesize *)
module mkCommentOnRulesInFunc();

   Reg#(Bool) b <- mkRegU;
   Reg#(Bool) x <- mkRegU;
   Reg#(Bool) y <- mkRegU;

   addRules(mkR(b,x,y));

endmodule

