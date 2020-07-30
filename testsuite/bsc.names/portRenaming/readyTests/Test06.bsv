typedef Bit#(10) Type;

interface IFC#(type mType);
  (* ready = "st$ready" *)
 method Action start(mType a, mType b);
  (* ready = "res$ready" *)
 method mType result(mType c);
  (* ready = "ch$ready" *)
 method ActionValue#(mType) check(mType d);
endinterface

(* synthesize *)
module mkDesign_06 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action start(a,b);
    val <= a;
    res <= b;
  endmethod	

  method Type result(c);
     return res+c;
  endmethod	
  	 
  method ActionValue#(Type) check(d);
    val <= val + 1;
    res <= res + 2;
	return res+d;
  endmethod	
	
endmodule
