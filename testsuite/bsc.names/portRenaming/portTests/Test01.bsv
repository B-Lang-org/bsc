typedef Bit#(5) Type;

interface IFC#(type mType);
 method Action start((* port = "sta" *) mType a, (* port = "stb" *) mType b);
 method mType result((* port = "stc" *) mType c);
 method ActionValue#(mType) check((* port = "std" *) mType d);
endinterface

(* synthesize *) 
module mkDesign_01 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action start(a, b);
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
