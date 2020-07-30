import List::*;

interface Property#(parameter type a);
  method ActionValue#(a) advance(a d);
endinterface

module mkTestProp (Property#(int));

  method ActionValue#(int) advance (int data);
    return 0;
  endmethod
endmodule


interface Assertion#(parameter type a);
  method Action advance(a d);
endinterface


module mkAssert#(Integer n) (Assertion#(int));
  
  List#(Property#(int)) ps <- replicateM(n, mkTestProp);
  int len = fromInteger(n);
  
  method Action advance (int data);
  action
    int pres = 1;
    //for (Integer k = 0; fromInteger(k) < len; k = k + 1) //This works
    for (Integer k = 0; fromInteger(k) <= len; k = k + 1) //This doesn't work
    begin
      pres <- (ps[k]).advance(data);
    end 
  endaction
  endmethod
  
endmodule

(* synthesize *)
module mkTest ( Empty );

  Reg#(int) x <- mkReg(0);

  function Bool lambda(int y);
    if ((y & 1) == 1) return True; else return False; 
  endfunction
  
  Assertion#(int) as <- mkAssert(5);

  rule foo (True);
   x <= x + 1;
   as.advance(x);
  endrule
endmodule
