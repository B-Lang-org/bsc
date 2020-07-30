//Signal from Argument to Ready of the same method method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag!

package Argument2Rdy2;

import FIFO :: *;

interface Argument2Rdy2Interv;
    method Action start (Bit #(8) inp);
    method Bit #(1) rdy_start();
endinterface

import "BVI" Imported_Verilog =
    module mksubArgument2Rdy2v(Argument2Rdy2Interv);
        method start (Inpt) enable(En_start);
        method Rdy_start rdy_start();
        path (Inpt, Rdy_start);
    endmodule
        
interface Argument2Rdy2Inter;
    method Action start (Bit #(8) inp);
endinterface

(* synthesize, always_enabled *)

module [Module] mksubArgument2Rdy2(Argument2Rdy2Inter);

 
    Argument2Rdy2Interv dut();
    mksubArgument2Rdy2v the_dut (dut);

    method Action start (inp) if (dut.rdy_start == 1);
      dut.start(inp);
    endmethod
    
   
endmodule

(* synthesize *)

module [Module] mkArgument2Rdy2 ();
    
    Argument2Rdy2Inter dut();
    mksubArgument2Rdy2 the_dut(dut);
   
    rule always_fire ;
        dut.start(?);
    endrule
       
endmodule
    

endpackage
