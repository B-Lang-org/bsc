(* synthesize *)
module mkCommentOnInlinedSubmodInForLoop();

   for (Integer i=0; i<3; i=i+1) begin
      (* doc="This is the submodule" *)
      //Reg#(Bool) sub <- mkSub;
      Reg#(Bool) sub();
      mkSub the_sub(sub);
   end

endmodule

module mkSub (Reg#(Bool));
   Reg#(Bool) r <- mkRegU;
   return r;
endmodule

