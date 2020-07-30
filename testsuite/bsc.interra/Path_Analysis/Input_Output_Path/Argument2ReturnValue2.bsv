//Signal from Argument to Return value of the same method, 
//Uses ActionValue
//A Bug for the time being

package Argument2ReturnValue2;

import FIFO :: *;

interface Argument2ReturnValue2Inter;
    method ActionValue #(Bit #(8)) start (Bit #(8) inp);
endinterface

(* synthesize *)

module mkArgument2ReturnValue2(Argument2ReturnValue2Inter);
    
    FIFO #(Bit #(8)) my_fifo();
    mkFIFO the_my_fifo (my_fifo);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule always_fire;
        counter <= counter + 1;
    endrule

    method ActionValue #(Bit #(8)) start (Bit #(8) inp);
        my_fifo.enq (counter);
        return (inp);
    endmethod
    
endmodule


endpackage
