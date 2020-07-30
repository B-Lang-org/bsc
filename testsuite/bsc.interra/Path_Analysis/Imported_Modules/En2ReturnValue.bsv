//In the sub-module, signal from Enable of one method 
//goes through combinational logic to ReturnValue of another method.
//In the toplevel module, a path is created from the return value
//to the enable signal


package En2ReturnValue;

import FIFO :: *;


interface En2ReturnValueInter;
    method Action start ();
    method Bit #(8) result();
endinterface


import "BVI" Imported_Verilog = 
    module mksubEn2ReturnValue (En2ReturnValueInter);
        method start() enable(En_start);
        method Result result();
        path (En_start, Result);
    endmodule

(* synthesize *)
module [Module] mkEn2ReturnValue ();
    
    En2ReturnValueInter dut();
    mksubEn2ReturnValue the_dut(dut);
   
    rule fire (dut.result >= 5);
        dut.start;
    endrule
       
endmodule
    

endpackage
