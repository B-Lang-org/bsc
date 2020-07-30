// Enable signal from one method to the Ready of another. 
// Should show using -dpathsPostSched flag

package MuxMethods1;

interface ArithIO ;
    method Action setInput1(Bit #(8) a);
    method Action setInput2(Bit #(8) a);
    method Bit #(8) getOutput();
endinterface: ArithIO

(* synthesize *)
module mkMuxMethods1(ArithIO);

    RWire #(Bit #(8)) x();
    mkRWire the_x (x);
    
    method Action setInput1(a);
        x.wset (a);
    endmethod: setInput1 
    
    method Action setInput2(a); 
        x.wset (a+1);
    endmethod: setInput2

    method getOutput() if (unJust (x.wget) >=4);
       getOutput = unJust (x.wget);
    endmethod

endmodule


endpackage
