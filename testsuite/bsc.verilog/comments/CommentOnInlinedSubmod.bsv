
(* synthesize *)
module mkCommentOnInlinedSubmod ();
   (* doc="This is the submodule" *)
   //Reg#(Bool) sub <- mkSub;
   Reg#(Bool) sub();
   mkSub the_sub(sub);
endmodule

module mkSub (Reg#(Bool));
   Reg#(Bool) r <- mkRegU;
   return r;
endmodule

