typedef Bit#(5) Type;

interface IFC#(type mType);
  (* prefix = "" *)
 method Action one(mType a, mType b);
  (* prefix = "" *)
 method mType two((* port = "a" *) mType g_a);
endinterface

(* synthesize *)
module mkDesign_06 (IFC#(Type));

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
