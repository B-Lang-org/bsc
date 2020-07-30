//Signal from Argument to Ready of another method, 
//Should be reported when using -dpathsPostSched flag


package Argument2Rdy;

import FIFO :: *;

interface Argument2RdyInter;
    method Action start (Bit #(8) inp);
    method Bit #(8) result();
endinterface

(* synthesize *)

module mkArgument2Rdy(Argument2RdyInter);
    
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
    
    method result if (x.wget == Just (5) || x.wget == Nothing);
        return (my_fifo.first);
    endmethod
   
endmodule

    

endpackage
