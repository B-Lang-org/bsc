
(* synthesize *)
(* doc="This is the top" *)
module mkCommentOnInlinedModule ();
   Reg#(Bool) sub <- mkSub;
endmodule

(* doc="This is the submodule" *)
module mkSub (Reg#(Bool));
endmodule

