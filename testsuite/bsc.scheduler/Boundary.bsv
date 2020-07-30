interface SubIFC;
   method Action incr();
endinterface

function ActionValue#(Bit#(64)) adjusted(int dummy);
   actionvalue
     Bit#(64) t <- $time();
     if (genVerilog) return (t + 5);
     else return t;
   endactionvalue
endfunction

(* synthesize *)
module mkBoundary_Sub (SubIFC);
   Reg#(int) rg <- mkReg(0);

   rule sub_rule;
      $display("%t: sub", adjusted(0));
      rg <= rg + 2;
   endrule
   
   method Action incr();
      rg <= rg + 1;
   endmethod
endmodule

(* synthesize *)
module sysBoundary();
   SubIFC s <- mkBoundary_Sub;

   Reg#(Bool) q <- mkReg(True);
   Reg#(UInt#(8)) count <- mkReg(0);
   
   rule top_rule;
      q <= !q;
      if (q)
	 s.incr;
   endrule
   
   rule incr;
      if (count > 100) $finish(0);
      count <= count + 1;
   endrule
   
endmodule
