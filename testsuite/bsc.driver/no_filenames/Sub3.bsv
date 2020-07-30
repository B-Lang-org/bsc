(* synthesize *)
module mkSub3();
   Reg#(Bool) x <- mkReg(True);

   rule flip;
      $display("%m: x = %b", x);
      x <= !x;
   endrule: flip
   
endmodule: mkSub3
