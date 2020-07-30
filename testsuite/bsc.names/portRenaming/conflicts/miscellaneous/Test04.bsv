typedef Bit#(5) Type;

interface IFC#(type mType);
  (* prefix = "g" *)
 method Action one(mType a, (* port = "a" *)mType b);
 method mType two(mType g_a);
endinterface

(* synthesize *)
module mkDesign_04 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action one(a,b);
    val <= a;
    res <= b;
  endmethod	

  method Type two(g_a);
     return res+g_a;
  endmethod	
  	 
	
endmodule
