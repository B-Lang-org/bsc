(* synthesize *)
module sysMERulesInSubmod ();
   Empty x <- mkMERulesInSubmod_Sub;
endmodule

(* synthesize *)
module mkMERulesInSubmod_Sub ();

   Reg#(Bool) b <- mkRegU;
   RWire#(Bool) rw <- mkRWire;

   rule r1 (b);
      b <= False;
      rw.wset(True);
   endrule

   rule r2 (!b && isJust(rw.wget));
      b <= True;
   endrule

endmodule
