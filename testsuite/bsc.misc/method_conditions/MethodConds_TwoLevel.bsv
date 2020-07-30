(* synthesize *)
module sysMethodConds_TwoLevel();
   Reg#(Bit#(8)) s <- mkMethodConds_TwoLevel_Sub;

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   rule r;
      if (c1)
         s <= 0;
      else if (c2)
         s <= 1;
   endrule
endmodule

module mkMethodConds_TwoLevel_Sub(Reg#(t)) provisos (Bits#(t,szt));
   Reg#(t) rg <- mkRegU;

   method Action _write(t x);
      rg <= x;
   endmethod

   method t _read();
      return rg;
   endmethod
endmodule
