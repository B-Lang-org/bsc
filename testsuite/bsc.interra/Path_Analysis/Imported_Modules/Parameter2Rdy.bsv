//Signal from Parameter to Ready of a method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag

package Parameter2Rdy;

import FIFO :: *;

interface Parameter2RdyInterv;
    method Bit #(8) result();
    method Bit #(1) rdy_result();
endinterface

import "BVI" Imported_Verilog = 
    module mksubParameter2Rdyv #(Bit #(8) param) (Parameter2RdyInterv);
        method Result result();
        method Rdy_result rdy_result();
        schedule (result, rdy_result) CF (result, rdy_result);
    endmodule

interface Parameter2RdyInter;
    method Bit #(8) result();
endinterface

(* synthesize *)
module [Module]  mksubParameter2Rdy #(Bit #(8) param) (Parameter2RdyInter);
    
    Parameter2RdyInterv dut();
    mksubParameter2Rdyv #(param) the_dut(dut);
   
    method result if (dut.rdy_result == 1);
        return (dut.result);
    endmethod
endmodule


(* synthesize,
   descending_urgency = "fire_when_result_ready, fire_when_result_not_ready" *)
module [Module] mkParameter2Rdy ();
    
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
