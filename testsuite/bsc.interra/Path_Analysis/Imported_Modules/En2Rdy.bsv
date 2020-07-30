//Signal from Enable of one method to Ready of another, both methods are then called in the 
//same rule.
//Should report an error with -verilog flag

package En2Rdy;

import FIFO :: *;

interface En2RdyInterv;
    method Action start ();
    method Bit #(8) result();
    method Bit #(1) rdy_result();
endinterface

interface En2RdyInter;
    method Action start();
    method Bit #(8) result();
endinterface

import "BVI" VerilogModule = 

  module  mksubEn2Rdyv(En2RdyInterv);
   
   method start() enable(En_start);
   method Result result();
   method Rdy_result rdy_result();
   path (En_start, Rdy_result);
   schedule (result, rdy_result) CF (result, rdy_result);
   schedule start SBR rdy_result;   
  endmodule

(* synthesize *)
module [Module] mksubEn2Rdy (En2RdyInter);
   En2RdyInterv dut();
   mksubEn2Rdyv the_dut(dut);

   method Action start();
       dut.start();
   endmethod

   method result() if (dut.rdy_result == 1);
       return (dut.result);
   endmethod

endmodule


(* synthesize *)
module [Module] mkEn2Rdy ();
    
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
