package MkBGPd;

import BGetPut :: *;
import GetPut :: *;
import Connectable :: *;

module mkDesign(BGetPut #(Bit #(8))) ;
   let x <- mkBGetPut;
   return(x);
endmodule: mkDesign

endpackage : MkBGPd
