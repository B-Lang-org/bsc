import S1 :: * ;

typedef Bit#(10) Type;

interface IFC#(type mType);
  method Action start(mType a, mType b);
  (* always_ready *)
  interface S1#(mType) subIFC;
endinterface

(* synthesize *)
module mkDesign_06 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action start(a,b);
    val <= a;
    res <= b;
  endmethod	

  interface S1 subIFC;
    method Type result(c);
       return res+c;
    endmethod	
  	 
    method ActionValue#(Type) check(d);
      val <= val + 1;
      res <= res + 2;
	  return res+d;
    endmethod	
  endinterface
	
endmodule
