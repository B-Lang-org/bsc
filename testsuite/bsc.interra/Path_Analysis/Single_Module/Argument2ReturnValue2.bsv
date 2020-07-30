//Signal from Argument to Return value of the same method, 
//The combinational loop is completed at the top level
//Uses ActionValue
//Should report an error with -verilog flag

package Argument2ReturnValue2;

import FIFO :: *;

interface Argument2ReturnValue2Inter;
    method ActionValue #(Bit #(8)) start (Bit #(8) inp);
endinterface


module mksubArgument2ReturnValue2(Argument2ReturnValue2Inter);
    
    FIFO #(Bit #(8)) my_fifo();
    mkFIFO the_my_fifo (my_fifo);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    rule always_fire;
        counter <= counter + 1;
    endrule

    method ActionValue #(Bit #(8)) start (inp);
        my_fifo.enq (counter);
        return (inp);
    endmethod
    
endmodule

(* synthesize *)

module mkArgument2ReturnValue2 ();
    
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
