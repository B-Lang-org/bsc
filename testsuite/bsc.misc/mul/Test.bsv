interface Mul;
  method Bit#(64) mul(Bit#(128) a, Bit#(128) b, Bool x);
endinterface

(* synthesize *)
module sysTest();
   Mul m <- mkMul;
   
   Reg#(Bool) b <- mkReg(False);
   Reg#(Bit#(128)) x <- mkReg(18074723);
   Reg#(Bit#(128)) y <- mkReg(93847236);
   Reg#(UInt#(8)) count <- mkReg(0);
   
   rule go (count < 50);
      $display("%d: x=%0d y=%0d", count,x,y);
      if (b)
	 x <= x + extend(m.mul(x,y,b));
      else
	 y <= y + extend(m.mul(x,y,b));
      b <= !b;
      count <= count + 1;
   endrule
   
   rule done (count >= 50);
      $finish(0);
   endrule
endmodule

module mkMul(Mul);
   method Bit#(64) mul(Bit#(128) a, Bit#(128) b, Bool x);
      Bit#(128) prod = a*b;
      Bit#(64) c = case (x)
                      True: truncate(prod);
                      False: prod[127:64];
                   endcase;
      return c;
   endmethod    
endmodule
