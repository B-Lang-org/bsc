//Signal from Parameter to Return value of another method, 
//The combinational loop is completed at the top level
//through two rules
//Should report an error with -verilog flag

package Parameter2ReturnValue;

import FIFO :: *;

interface Parameter2ReturnValueInter;
    method Bit #(8) result();
endinterface

(* synthesize *)

module mksubParameter2ReturnValue #(Bit #(8) param) (Parameter2ReturnValueInter);
    
    method result;
        return (param);
    endmethod
   
endmodule

(* synthesize *)
module mkParameter2ReturnValue ();
    
    RWire #(Bit #(8)) inwire();
    mkRWire the_inwire (inwire);
    
    Bit #(8) param = inwire.wget matches tagged Just {.x} ? x : 0;
    
    Parameter2ReturnValueInter dut();
    mksubParameter2ReturnValue #(param) the_dut(dut);
   
    rule always_fire;
        inwire.wset(dut.result); 
    endrule

       
endmodule
    

endpackage
