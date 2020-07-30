import Vector :: * ;
import List :: * ;

typedef Bit#(5) Type;

interface S1#(type mType);
 method Action start(mType a, mType b);
 method mType result(mType c);
 method ActionValue#(mType) check(mType d);
endinterface

module mkGen (S1#(pType)) provisos(Bits#(pType,sa),Arith#(pType));
  Reg#(pType) val <- mkReg(0);
  Reg#(pType) res <- mkReg(0);

  method pType result(c);
    return res+c;
  endmethod	
  	 
  method ActionValue#(pType) check(d);
    val <= val + 1;
    res <= res + 2;
  return res+d;
  endmethod
  
  method Action start(a,b);
    val <= a;
    res <= b;
  endmethod	
endmodule  


interface IFC#(type aType);
 (* prefix = "XYZ" *)
 interface Vector#(3,S1#(aType))  subIFC;
endinterface

(* synthesize *) 
module mkDesign_11 (IFC#(Type));

  Vector#(3,S1#(Type)) interfaces = newVector;
  interfaces <- replicateM(mkGen);
	 
  
  interface subIFC = interfaces;


  
endmodule
