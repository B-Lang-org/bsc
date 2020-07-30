//Signal from Parameter to Return value of another method, 
//Should report when using the -dpathsPostSched flag

package Parameter2ReturnValue;

import FIFO :: *;

interface Parameter2ReturnValueInter;
    method Bit #(8) result();
endinterface

(* synthesize *)

module mkParameter2ReturnValue #(Bit #(8) param) (Parameter2ReturnValueInter);
    
    method result;
        return (param);
    endmethod
   
endmodule


endpackage
