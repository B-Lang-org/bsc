(* synthesize *)
module sysMERuleAndMethodInSubmod ();
   Empty x <- mkMERuleAndMethodInSubmod_Sub1;
endmodule

(* synthesize *)
module mkMERuleAndMethodInSubmod_Sub1 ();

   SubIFC s <- mkMERuleAndMethodInSubmod_Sub2;

   rule r1;
      s.m;
   endrule

endmodule

interface SubIFC;
   method Action m;
endinterface

(* synthesize *)
module mkMERuleAndMethodInSubmod_Sub2 (SubIFC);

   Reg#(Bool) b <- mkRegU;
   RWire#(Bool) rw <- mkRWire;

   rule r2 (!b && isJust(rw.wget));
      b <= False;
   endrule
   
   method Action m () if (b);
      b <= False;
      rw.wset(True);
   endmethod

endmodule
   
