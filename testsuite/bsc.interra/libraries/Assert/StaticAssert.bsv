package StaticAssert;

import Assert:: *;
import EqFunction :: *;
import Tabulate :: *;

function Bit #(6) add (Bit #(3) a, Bit #(3) b) ;
    return (zeroExtend(a)+zeroExtend(b));
endfunction: add

function Bit #(6) add2 (Bit #(3) a, Bit #(3) b) ;
    return (zeroExtend(a+b));
endfunction: add2

function  (Bit #(6)) tabulated_add (Bit #(3) a, Bit #(3) b);
    return ((tabulate (add)) (a,b)) ;
endfunction: tabulated_add


module mkTestbench_StaticAssert ();
        
  Reg#(Bit#(6)) counter <- mkReg(0);
  Reg#(Bool) fail1 <- mkReg(False);
 
  
  staticAssert (add2 == tabulated_add, "Failure: Add2 != Tabulated_Add");
  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule display_values (True);
     $display ("A = %d, B= %d, A+B = %d", counter[5:3], counter[2:0], tabulated_add(counter[5:3], counter[2:0]));
  endrule

  
endmodule: mkTestbench_StaticAssert 
endpackage: StaticAssert
