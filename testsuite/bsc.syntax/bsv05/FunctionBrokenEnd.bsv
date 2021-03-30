function Reg#(a) func(Bool b, Reg#(a) x1, Reg#(a) x2)
                     provisos (Bits#(a,sa), Arith#(a));
    func = b ? x1 : x2;
endfunction: foobar



