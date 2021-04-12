(* synthesize *)
module mkTest();
   Reg#(Bit#(16)) rg <- mkRegU;
   rule r1;
      Bool c = ?;
      Bit#(16) v;
      if (c) v = 1; else v = 2;
      rg <= v;
   endrule
endmodule
