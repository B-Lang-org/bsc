//Signal from Parameter to Ready of a method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag !


package Parameter2Rdy;

import FIFO :: *;

interface Parameter2RdyInter;
    method Bit #(8) result();
endinterface

(* synthesize *)
module mksubParameter2Rdy #(Bit #(8) param) (Parameter2RdyInter);
    
    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    rule always_fire;
        counter <= counter + 1;
    endrule

    method result if (param >= 5 );
        return (counter);
    endmethod
   
endmodule

(* synthesize,
   descending_urgency = "fire_when_result_ready, fire_when_result_not_ready" *)

module mkParameter2Rdy ();
    
    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    Bit #(8) param = inwire.wget matches tagged Just {.x} ? x : 6;
    
    Parameter2RdyInter dut();
    mksubParameter2Rdy #(param) the_dut(dut);
   
    
    rule fire_when_result_ready;
        Bit #(8) temp = dut.result();
        inwire.wset (temp);
        $display ("Result = %d", dut.result );
    endrule

    rule fire_when_result_not_ready;
        inwire.wset (6);
    endrule
       
endmodule
    

endpackage
