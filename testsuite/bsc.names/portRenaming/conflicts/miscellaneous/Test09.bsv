
interface S1#(type aA);
  (* prefix = "result" *)
 method aA result(aA c);
  (* prefix = "check" *)
 method ActionValue#(aA) check(aA d);
endinterface

interface IFC#(type anyType);
  (* prefix = "subIFC_result" *)
 method anyType result(anyType c);
  (* prefix = "subIFC_check" *)
 method ActionValue#(anyType) check(anyType d);
 method Action start(anyType a, anyType b);
 interface S1#(anyType) subIFC;
endinterface

typedef Bit#(5) Type;

(* synthesize *) 
module mkDesign_09 (IFC#(Type));

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
