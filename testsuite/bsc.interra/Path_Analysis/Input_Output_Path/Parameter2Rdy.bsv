//Signal from Parameter to Ready of a method, 
//Should show when using the -dpathsPostSched flag

package Parameter2Rdy;

import FIFO :: *;

interface Parameter2RdyInter;
    method Bit #(8) result();
endinterface

(* synthesize *)
module mkParameter2Rdy #(Bit #(8) param) (Parameter2RdyInter);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    rule always_fire;
        counter <= counter + 1;
    endrule

    method result if (param >= 5 );
        return (counter);
    endmethod
   
endmodule

    

endpackage
