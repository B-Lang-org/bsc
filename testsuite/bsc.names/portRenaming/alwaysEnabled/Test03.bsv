typedef Bit#(7) Type;

interface S1#(type aA);
 method aA result(aA c);
 method ActionValue#(aA) check(aA d);
endinterface

interface IFC#(type bB);
 method Action start(bB a, bB b);
  (* always_enabled *)
 interface S1#(bB) subIFC;
endinterface

(* synthesize *)
module mkDesign_03 (IFC#(Type));

  Reg#(Type) val <- mkReg(0);
  Reg#(Type) res <- mkReg(0);


  method Action start(a,b);
    val <= a;
    res <= b;
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
