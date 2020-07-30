typedef Bit#(11) Type;

interface IFC#(type mType);
 method Action start((* port = "sta_1" *) mType a, (* port = "stb_1" *) mType b);
 method mType result((* port = "stc_1" *) mType c);
 method ActionValue#(mType) check((* port = "std_1" *) mType d);
endinterface

(* synthesize *) 
module mkDesign_07 (IFC#(Type));

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
