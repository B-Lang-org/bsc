//In the sub-module, signal from Enable of one method 
//goes through combinational logic to ReturnValue of the same method.
//Should show when using the -dpathsPostSched flag


package En2ReturnValue2;

import FIFO :: *;

interface En2ReturnValue2Inter;
    method ActionValue #(Bit #(8)) start ();
endinterface

(* synthesize *)
module mkEn2ReturnValue2(En2ReturnValue2Inter);
    
    FIFO #(Bit #(8)) my_fifo();
    mkFIFO the_my_fifo (my_fifo);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule always_fire;
        counter <= counter + 1;
    endrule

    method start;
     actionvalue
        x.wset (counter);
        Bit #(8) temp;
        if (x.wget matches tagged Just {.y})
            temp = y;
        else
            temp = 0;
        return temp;
     endactionvalue
    endmethod
    
   
endmodule

    

endpackage
