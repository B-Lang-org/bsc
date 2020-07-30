(* synthesize *)
module mkCommentOnSubmodInFunc();
   Reg#(Bool) r1 <- mkSub;
endmodule

function Module#(Reg#(Bool)) mkSub();
   module#(Reg#(Bool)) m = module#(Reg#(Bool));
			      (* doc = "This is a register" *)
			      Reg#(Bool) r <- mkRegU;
			      return r;
			   endmodule;
   return m;
endfunction

