//Signal from Argument to Ready of the same method method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag

package Argument2Rdy2;

import FIFO :: *;

interface Argument2Rdy2Inter;
    method Action start (Bit #(8) inp);
endinterface


module mksubArgument2Rdy2(Argument2Rdy2Inter);
    
    FIFO #(Bit #(8)) my_fifo();
    mkFIFO the_my_fifo (my_fifo);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule always_fire;
        counter <= counter + 1;
    endrule

    method Action start (inp) if (x.wget == Just (5));
        my_fifo.enq (counter);
        x.wset (inp);
    endmethod
    
   
endmodule

(* synthesize *)
module mkArgument2Rdy2 ();
    
    Argument2Rdy2Inter dut();
    mksubArgument2Rdy2 the_dut(dut);
   
    rule always_fire ;
        dut.start(?);
    endrule
       
endmodule
    

endpackage
