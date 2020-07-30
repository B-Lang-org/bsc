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

(* synthesize *)

module mksubsubArgument2ReturnValue(Argument2ReturnValueInter);
    
    FIFO #(Bit #(8)) my_fifo();
    mkFIFO the_my_fifo (my_fifo);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule always_fire;
        counter <= counter + 1;
    endrule

    method Action start (inp);
        my_fifo.enq (counter);
        x.wset (inp);
    endmethod
    
    method result;
        return (unJust (x.wget));
    endmethod
   
endmodule

(* synthesize *)

module mksubArgument2ReturnValue (Argument2ReturnValueInter);
    Argument2ReturnValueInter dut();
    mksubsubArgument2ReturnValue the_dut(dut);

    method Action start (inp);
        dut.start (inp);
    endmethod

    method result;
        return (dut.result);
    endmethod

endmodule

(* synthesize *)
module mkArgument2ReturnValue ();
    
    Argument2ReturnValueInter dut();
    mksubArgument2ReturnValue the_dut(dut);
   
    rule always_fire;
        dut.start(dut.result); 
    endrule

       
endmodule
    

endpackage
