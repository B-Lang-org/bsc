//Signal from Argument to Ready of another method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag

package Argument2Rdy;

import FIFO :: *;

interface Argument2RdyInterv;
    method Action start (Bit #(8) inp);
    method Bit #(8) result;
    method Bit #(1) rdy_result;
endinterface

import "BVI" Imported_Verilog =
    module mksubArgument2Rdyv (Argument2RdyInterv);
        method start (Inpt) enable(En_start);
        method Result result();
        method Rdy_result rdy_result();
        path (Inpt, Rdy_result);
        schedule (result, rdy_result) CF (result,rdy_result);
	schedule start SBR rdy_result;
    endmodule

interface Argument2RdyInter;
    method Action start (Bit #(8) inp);
    method Bit #(8) result();
endinterface

(* synthesize *)

module [Module] mksubArgument2Rdy(Argument2RdyInter);
    
    Argument2RdyInterv dut();
    mksubArgument2Rdyv the_dut (dut);

    method Action start (a);
        dut.start(a);
    endmethod

    method result if (dut.rdy_result == 1);
        return (dut.result);
    endmethod
   
endmodule

(* synthesize *)
module mkArgument2Rdy ();
    
    Argument2RdyInter dut();
    mksubArgument2Rdy the_dut(dut);
   
    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    rule fire_when_result_ready (dut.result == 5);
        Bit #(8) temp = dut.result();
        inwire.wset (temp);   
    endrule

    Bit #(8) cond = inwire.wget matches tagged Just {.x} ? 1 : 0;

    rule always_fire ;
        dut.start(cond);
    endrule
       
endmodule
    

endpackage
