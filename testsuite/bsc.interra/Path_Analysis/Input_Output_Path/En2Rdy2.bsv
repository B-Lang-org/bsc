//Signal from Enable to Ready, both methods are then called in the 
//separate rules, with wrong urgency order.
//Should report an error with -verilog flag.

package En2Rdy2;

import FIFO :: *;

interface En2Rdy2Inter;
    method Action start ();
    method Bit #(8) result();
endinterface

(* synthesize *)
module mksubEn2Rdy2(En2Rdy2Inter);
    
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

(* descending_urgency = "fire2, fire1", synthesize *)
module mkEn2Rdy2 ();
    
    En2Rdy2Inter dut();
    mksubEn2Rdy2 the_dut(dut);
   
    // for the urgency attribute to matter, the rules need to conflict;
    // this register is just to make it conflict
    Reg#(Bit#(8)) rg <- mkRegU;

    rule fire1;
        rg <= rg + 1;
        dut.start;
    endrule

    rule fire2;
        Bit #(8) temp = dut.result();
        $display ("Temp = %d", temp);
        rg <= rg + temp;
    endrule
       
endmodule
    

endpackage
