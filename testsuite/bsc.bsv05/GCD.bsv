typedef UInt#(51) GCDInt;

interface ArithIO #(parameter type a);
    method Action setInput(a x, a y);
    method a getOutput();
endinterface: ArithIO

module mkGCD(ArithIO#(GCDInt));
    Reg#(GCDInt) x();
    mkReg#(?) the_x(x);

    Reg#(GCDInt) y();
    mkReg#(0) the_y(y);

    rule flip (x > y && y != 0);
        x <= y;
        y <= x;
    endrule

    rule sub (x <= y && y != 0);
        y <= y - x;
    endrule

    method Action setInput(GCDInt a, GCDInt b) if (y == 0);
        action
            x <= a;
            y <= b;
        endaction
    endmethod: setInput

    method GCDInt getOutput() if (y == 0);
        getOutput = x;
    endmethod: getOutput
endmodule: mkGCD

