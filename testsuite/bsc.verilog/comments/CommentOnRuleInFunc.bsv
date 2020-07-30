
function Rules mkR(Bool b, Reg#(Bool) x);
   return (rules
	      (* doc = "This rule is important" *)
	      rule do_something (b);
		 x <= !x;
	      endrule
	   endrules);
endfunction


(* synthesize *)
module mkCommentOnRuleInFunc();

   Reg#(Bool) b <- mkRegU;
   Reg#(Bool) x <- mkRegU;

   addRules(mkR(b,x));

endmodule

