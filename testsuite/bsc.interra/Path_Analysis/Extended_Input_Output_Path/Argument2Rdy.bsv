//Signal from Argument to Ready of another method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag

package Argument2Rdy;

import FIFO :: *;

interface Argument2RdyInter;
    method Action start (Bit #(8) inp);
    method Bit #(8) result();
endinterface

(* synthesize *)

module mksubsubArgument2Rdy(Argument2RdyInter);
    
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

(* synthesize *)

module mksubArgument2Rdy(Argument2RdyInter);

    Argument2RdyInter dut();
    mksubsubArgument2Rdy the_dut(dut);
    
    method Action start (inp);
        dut.start(inp);
    endmethod

    method result;
        return (dut.result);
    endmethod

endmodule

(* synthesize *)
module mkArgument2Rdy ();
    
    Argument2RdyInter dut();
    mksubArgument2Rdy the_dut(dut);
   
    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    rule fire_when_result_ready;
        Bit #(8) temp = dut.result();
        inwire.wset (temp);   
    endrule

    rule always_fire (inwire.wget matches tagged Just {.x});
        dut.start(x);
    endrule
       
endmodule
    

endpackage
