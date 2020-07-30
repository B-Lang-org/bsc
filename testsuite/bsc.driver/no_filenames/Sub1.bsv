(* synthesize *)
module mkSub1();
   Reg#(Bool) x <- mkReg(False);

   rule flip;
      $display("%m: x = %b", x);
      x <= !x;
   endrule: flip
   
endmodule: mkSub1