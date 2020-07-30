//In the sub-module, signal from Enable of one method 
//goes through combinational logic to ReturnValue of another method.
//Should report when using the -dpathsPostSched flag


package En2ReturnValue;

import FIFO :: *;

interface En2ReturnValueInter;
    method Action start ();
    method Bit #(8) result();
endinterface

(* synthesize *)
module mkEn2ReturnValue(En2ReturnValueInter);
    
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
    
    method result;
        Bit #(8) temp;
        if (x.wget matches tagged Just {.y})
           temp = y;
        else
           temp = 0;
        return temp;
    endmethod
   
endmodule


endpackage
