//Signal from Argument to Return value of the same method, 
//The combinational loop is completed at the top level
//Should report an error with -verilog flag

package Argument2ReturnValue2;

import FIFO :: *;

interface Argument2ReturnValue2Interv;
    method Action start (Bit #(8) inp);
    method Bit #(8) result();
endinterface

import "BVI" Imported_Verilog =
    module mkArgument2ReturnValue2v (Argument2ReturnValue2Interv);
        method start (Input) enable(En_Input);
        method Result result();
        path (Input, Result);
        schedule start SB result;
    endmodule

interface Argument2ReturnValue2Inter;
    method ActionValue #(Bit #(8)) start (Bit #(8) inp);
endinterface

(* synthesize *)

module [Module] mksubArgument2ReturnValue2(Argument2ReturnValue2Inter);
    
    Argument2ReturnValue2Interv dut();
    mkArgument2ReturnValue2v the_dut (dut);

    method ActionValue #(Bit #(8)) start (inp);
        dut.start (inp);
        return (dut.result);
    endmethod
    
endmodule

(* synthesize *)
module [Module] mkArgument2ReturnValue2 ();
    
    Argument2ReturnValue2Inter dut();
    mksubArgument2ReturnValue2 the_dut(dut);
  
    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    rule always_fire;
         Bit #(8) temp <- (dut.start(unJust (inwire.wget))); 
         inwire.wset (temp);
    endrule

       
endmodule
    

endpackage
