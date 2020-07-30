(* synthesize *)
module sysArrSelReal();
   Reg#(Bit#(2)) rg <- mkReg(1);
   Reg#(Bit#(64)) rg2 <- mkRegU;
   Real ns[4] = { 0.1, 0.2, 0.3, 0.4 };
   rule r;
      // This isn't really testing for Real, because the task will be
      // pushed into the arms of the case?
      rg2 <= $realtobits(ns[rg]);
      $display(realToString(ns[rg]));
   endrule
endmodule
