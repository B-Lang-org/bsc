typedef Bit#(5) Type;

interface S1#(type mType);
 method mType result(mType c);
 method ActionValue#(mType) check(mType d);
endinterface

interface IFC#(type aType);
 method Action start1(aType a, aType b);
 method Action start2(aType a, aType b);
 (* prefix = "" *)
 interface S1#(aType) subIFC1;
 (* prefix = "" *)
 interface S1#(aType) subIFC2;
endinterface

(* synthesize *)
module mkDesign_08 (IFC#(Type));

  Reg#(Type) val1 <- mkReg(0);
  Reg#(Type) res1 <- mkReg(0);

  Reg#(Type) val2 <- mkReg(0);
  Reg#(Type) res2 <- mkReg(0);


  method Action start1(a,b);
    val1 <= a;
    res1 <= b;
  endmethod	

  method Action start2(a,b);
    val2 <= a;
    res2 <= b;
  endmethod	

  interface S1 subIFC1;
    method Type result(c);
      return res1+c;
    endmethod	
  	 
    method ActionValue#(Type) check(d);
      val1 <= val1 + 1;
      res1 <= res1 + 2;
	  return res1+d;
    endmethod	
  endinterface

  interface S1 subIFC2;
    method Type result(c);
      return res2+c;
    endmethod	
  	 
    method ActionValue#(Type) check(d);
      val2 <= val2 + 1;
      res2 <= res2 + 2;
	  return res2+d;
    endmethod	
  endinterface
endmodule
