//Should report an error with -verilog flag

package Combo_Loop;

interface ArithIO ;
    method Action setInput1(Bit #(8) a);
    method Action setInput2(Bit #(8) a);
    method Bit #(8) getOutput();
endinterface: ArithIO

(* synthesize *)
module mkCombo_Loop(ArithIO);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    RWire #(Bit #(8)) y();
    mkRWire the_y (y);
    
    Reg #(Bit #(8)) temp();
    mkReg #(0) the_temp (temp);

    rule always_fire;
        temp <= temp + 1;
    endrule
   
    Bit #(8) cond1 = x.wget matches tagged Just {.a} ? a : 0;
    Bit #(8) cond2 = y.wget matches tagged Just {.a} ? a : 0;
    
    method Action setInput1(a) if (cond1 >= 2);
        y.wset (temp);
    endmethod: setInput1 
    
    method Action setInput2(a) if (cond2 >= 2);
        x.wset (temp);
    endmethod: setInput2
    
    method getOutput();
       getOutput = unJust (x.wget) + unJust (y.wget);
    endmethod

endmodule




endpackage
