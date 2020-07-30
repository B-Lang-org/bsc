
interface IFC#(type anyType);
 method Action start(anyType a, anyType b);
 (* prefix = "", always_ready, always_enabled, result ="ABC" *)
 method anyType result((* port = "ABC" *) anyType c);
 (* prefix = "", always_ready, always_enabled *)
 method ActionValue#(anyType) check((* port = "ABC" *) anyType d);
endinterface

typedef Bit#(5) Type;

(* synthesize *) 
module mkDesign_21 (IFC#(Type));

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
