export mkFib;
export mkFib8;

import FIFO::*;

function Reg#(a) func(Bool b, Reg#(a) x1, Reg#(a) x2)
                     provisos (Bits#(a,sa), Arith#(a));
    func = b ? x1 : x2;
endfunction

function Module#(Reg#(Bit#(8))) mkFib8();
    mkFib8 = mkFib;
endfunction

module mkFib(Reg#(a)) provisos(Bits#(a,sa), Arith#(a));
    Reg#(a) x(); mkReg#(1) the_x(x);
    Reg#(a) y(); mkReg#(1) the_y(y);
    Reg#(Bool) z(); mkReg#(True) the_z(z);

    rule unnamed (True);
        func(z,x,y) <= x + y; z <= !z;
    endrule

    method Action _write(a val);
        action
            x <= 1; y <= 1; z <= True;
        endaction
    endmethod: _write

    method a _read();
        _read = func(z,x,y)._read();
    endmethod: _read
endmodule: mkFib
