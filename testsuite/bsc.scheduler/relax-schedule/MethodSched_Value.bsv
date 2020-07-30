interface SubIFC;
   method Action incr();
   method Bool   get();
endinterface

(* synthesize *)
module mkMethodSched_Value_Sub (SubIFC);
   Reg#(int)    rg <- mkReg(0);
   RWire#(void) rw <- mkRWire;

   rule sub_rule;
      $display("%d sub", $time);
      rg <= rg + 2;
      rw.wset(?);
   endrule

   method Action incr();
      rg <= rg + 1;
   endmethod

   method Bool get();
      return (isValid(rw.wget));
   endmethod
endmodule

(* synthesize *)
module sysMethodSched_Value();
   SubIFC s <- mkMethodSched_Value_Sub;

   Reg#(Bool)  q  <- mkReg(True);
   Reg#(Bool)  x  <- mkReg(True);
   Wire#(Bool) dw <- mkDWire(False);

   rule top_rule3;
      dw <= True;
      x <= !x;
   endrule

   rule top_rule2 (s.get && x);
      $display("Hi");
   endrule

   rule top_rule1;
      q <= !q;
      if (q)
	 s.incr;
      $display(dw);
   endrule

endmodule
