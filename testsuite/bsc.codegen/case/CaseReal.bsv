(* synthesize *)
module sysCaseReal();
   Reg#(Bit#(2)) rg <- mkReg(1);
   Reg#(Bit#(64)) rg2 <- mkRegU;
   rule r;
      Real n;
      case (rg)
         0 : n = 0.1;
         1 : n = 0.2;
         2 : n = 0.3;
         default : n = 0.4;
      endcase
      // This isn't really testing for Real, because the task will be
      // pushed into the arms of the case?
      rg2 <= $realtobits(n);
      $display(realToString(n));
   endrule
endmodule
