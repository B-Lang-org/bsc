(* synthesize *)
module mkTest();
   Bit#(0) init;
   if (False)
      init = 0;
   Reg#(Bit#(0)) rg <- mkReg(init);
endmodule
