//Signal from Argument to Return value of the same method, 
//Uses a Pure Function
//Should show while using -dpathsPostSched flag

package Argument2ReturnValue3;

import FIFO :: *;

interface Argument2ReturnValue3Inter;
    method Bit #(8) start (Bit #(8) inp);
endinterface

(* synthesize *)

module mkArgument2ReturnValue3(Argument2ReturnValue3Inter);
    
    method start (inp);
        return (inp);
    endmethod
    
endmodule

    

endpackage
