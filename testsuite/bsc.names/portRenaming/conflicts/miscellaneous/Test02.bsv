typedef Bit#(5) Type;

interface IFC#(type mType);
  (* prefix = "g" *)
 method Action f(mType a, mType b);
 method mType g(mType a);
endinterface

(* synthesize *)
module mkDesign_02 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action f(a,b);
    val <= a;
    res <= b;
  endmethod	

  method Type g(a);
     return res+a;
  endmethod	
  	 
	
endmodule
