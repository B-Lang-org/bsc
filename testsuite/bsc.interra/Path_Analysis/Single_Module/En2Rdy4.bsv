//Signal from Enable to Ready, (Ready is in fact not of enable)
//Uses mkConnection to complete a loop
//Should report an error with -verilog flag

package En2Rdy4;

import FIFO :: *;
import GetPut :: *;
import Connectable :: *;

interface En2Rdy4Inter;
    interface Put #(Bit #(8)) intr_put;
    interface Get #(Bit #(8)) intr_get;
endinterface

module mksubEn2Rdy4 (En2Rdy4Inter); 
    
    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    Bool cond = x.wget matches tagged Just {.y} ? False : True;
    
    interface Put intr_put; 
      method Action put (a);
        x.wset (a);
      endmethod
     endinterface

    interface Get intr_get;
      method ActionValue #(Bit #(8)) get if (cond);
        noAction;
        return (5);
      endmethod
    endinterface
    
   
endmodule


(* synthesize *)
module mkEn2Rdy4 ();
    
    En2Rdy4Inter dut1();
    mksubEn2Rdy4 the_dut1(dut1);
    
    En2Rdy4Inter dut2();
    mksubEn2Rdy4 the_dut2(dut2);
  
    Get #(Bit #(8)) dut1_get = dut1.intr_get;
    Get #(Bit #(8)) dut2_get = dut2.intr_get;
    Put #(Bit #(8)) dut1_put = dut1.intr_put;
    Put #(Bit #(8)) dut2_put = dut2.intr_put;
    mkConnection (dut1_get, dut2_put);
    mkConnection (dut2_get, dut1_put);
   
endmodule
 

endpackage
