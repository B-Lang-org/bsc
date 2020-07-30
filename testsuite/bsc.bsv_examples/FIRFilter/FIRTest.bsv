package FIRTest;

import FIRMain::*;
import SyncFIR::*;

import Vector::*;

//A simple testbench to observe the outputs

//Set type, coefficients here
//proviso: TestType must be Arith, Bits
typedef Int#(16) TestType; 
typedef 4 CoefNum;
Vector#(CoefNum, TestType) initialCoefs;
initialCoefs = replicate(1);



module sysFIRTest ( Empty );

  Reg #(int) count();
  mkReg #(0) i_count(count);
  
  FIRFilter#(TestType, CoefNum) firtest();
  mkModularFIR i_firtest(firtest);
  Reg#(TestType) res <- mkReg(0);
  
  rule init (count == 0);
    firtest.setCoefs(initialCoefs);
    count <= count + 1;
  endrule
  
  rule stop (count >= 100);
    $finish(0);
  endrule
  
  rule action1 ((count < 100) && (count > 0));
    action
      Maybe#(TestType) r <- firtest.fir(truncate(count));
       if (isValid(r))
       begin
          res <= validValue(r);
	  $display("%0d" , res);
	  //A test condition would go here
       end
      count <= count + 1;
    endaction
  endrule
endmodule: sysFIRTest

endpackage: FIRTest
