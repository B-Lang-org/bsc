// Creates Loop. 
// Should show error using -verilog flag

package MuxLogic;

interface ArithIO ;
    method Action setInput1(Bit #(8) a);
    method Action setInput2(Bit #(8) a);
    method Bit #(8) getOutput();
endinterface: ArithIO

(* synthesize *)
module mksubMuxLogic(ArithIO);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    method Action setInput1(a);
        x.wset (a);
    endmethod: setInput1 
    
    method Action setInput2(a) if (unJust (x.wget) >= 4); 
        x.wset (a+1);
    endmethod: setInput2

    method getOutput();
       getOutput = unJust (x.wget);
    endmethod

endmodule

(* synthesize , descending_urgency = "alwaysfire1, alwaysfire2" *)
module mkMuxLogic();
    ArithIO dut();
    mksubMuxLogic the_dut (dut);

    Reg #(Bit #(8)) counter();
    mkReg #(0) the_my_reg (counter);
    
    rule increment;
        counter <= counter + 1;
    endrule
    
    rule alwaysfire1;
        dut.setInput1 (counter);
    endrule

    rule alwaysfire2;
        dut.setInput2 (counter + 1);
    endrule

    rule alwaysfire3;
        $display (dut.getOutput);
    endrule    
endmodule

endpackage
