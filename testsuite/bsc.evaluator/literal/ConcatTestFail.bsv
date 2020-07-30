(* synthesize *)
module sysConcatTestFail(Empty);
   
   Reg#(Bit#(5)) x <- mkReg(0);
   
   rule test;
      $display({1, x});
      $finish(0);
   endrule

endmodule
