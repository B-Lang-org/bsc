//Signal from Argument to Return value of another method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag

package Argument2ReturnValue;

import FIFO :: *;

interface Argument2ReturnValueInter;
    method Action start (Bit #(8) inp);
    method Bit #(8) result();
endinterface

import "BVI" Imported_Verilog = 
    module mksubArgument2ReturnValue (Argument2ReturnValueInter);
        method start (Input) enable(En_Input);
        method Result result();
        path (Input, Result);
        schedule result CF result;
    endmodule

(* synthesize *)
    
module [Module] mkArgument2ReturnValue ();
    
    Argument2ReturnValueInter dut();
    mksubArgument2ReturnValue the_dut(dut);
   
    rule always_fire;
        dut.start(dut.result); 
    endrule

       
endmodule
    

endpackage
