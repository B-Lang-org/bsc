//Signal from Enable of one method to Ready of another, both methods are then called in the 
//same rule.
//Should report an error with -verilog flag!

package En2Rdy;

import FIFO :: *;

interface En2RdyInter;
    method Action start ();
    method Bit #(8) result();
endinterface

module mksubEn2Rdy(En2RdyInter);
    
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

(* synthesize *)
module mkEn2Rdy ();
    
    En2RdyInter dut();
    mksubEn2Rdy the_dut(dut);
   
    rule always_fire;
    Bit #(8) temp;
        dut.start;
        temp = dut.result();
        $display ("Result = %d", temp);
    endrule
       
endmodule
    

endpackage
