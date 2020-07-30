typedef Bit#(5) Type;

interface IFC#(type mType);
  (* prefix = "g" *)
 method Action one(mType a, mType b);
  (* prefix = "g" *)
 method mType two(mType a);
endinterface

(* synthesize *)
module mkDesign_03 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action one(a,b);
    val <= a;
    res <= b;
  endmethod	

  method Type two(a);
     return res+a;
  endmethod	
  	 
	
endmodule
