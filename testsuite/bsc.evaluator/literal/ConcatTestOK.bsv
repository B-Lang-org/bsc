(* synthesize *)
module sysConcatTestOK(Empty);
   
   Reg#(Bit#(5)) x <- mkReg(0);
   
   rule test;
      $display({0, x});
      $finish(0);
   endrule

endmodule
