package Example;

// import XReg::*;
import Zaz::*;

interface TestIFC;
   interface CXReg#(Bit#(16)) a0;
endinterface

module mkTest#(TestIFC reg_set) (Empty);
   
   rule every;      
      reg_set.a0 <= reg_set.a0 + 1;
   endrule
   
endmodule
      
endpackage
