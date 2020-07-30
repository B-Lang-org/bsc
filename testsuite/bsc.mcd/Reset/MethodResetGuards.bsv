(* synthesize *)
module sysMethodResetGuards ();
   SubIFC s <- mkMethodResetGuards_Sub;
   Reg#(Bit#(16)) count <- mkReg(0);

   rule do_set;
      s.set(count);
      count <= count + 1;
   endrule
endmodule

interface SubIFC;
   method Action set(Bit#(16) c);
endinterface

(* synthesize *)
module mkMethodResetGuards_Sub(SubIFC);
   Reg#(Bit#(16)) rg <- mkReg(17);
   method Action set(Bit#(16) c);
      rg <= c;
      // if system tasks in methods are not guarded by reset,
      // then this display will execute during reset and the finish might
      // as well, depending on the value of 'c' (such as "aaaa")
      $display("count = %h", c);
      if (c > 10)
	 $finish(0);
   endmethod
endmodule

