//Signal from Enable to Ready of another method. 
//Should report when using the -dpathsPostSched flag.

package En2Rdy5;

import FIFO :: *;

interface En2Rdy5Inter;
    method Action start ();
    method Bit #(8) result();
endinterface

(* synthesize *)
module mkEn2Rdy5(En2Rdy5Inter);
    
    FIFO #(Bit #(8)) my_fifo();
    mkFIFO the_my_fifo (my_fifo);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule always_fire;
        counter <= counter + 1;
    endrule

    method Action start;
        my_fifo.enq (counter);
        x.wset (counter);
    endmethod
    
    method result if (x.wget matches tagged Just {.y});
        return (my_fifo.first);
    endmethod
   
endmodule


endpackage
