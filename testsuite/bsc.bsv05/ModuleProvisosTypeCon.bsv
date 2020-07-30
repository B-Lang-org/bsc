module mkFoo(Reg #(a)) provisos(Bits#(a,5), Arith#(a));
    method a _read(); return ?; endmethod
    method Action _write(a val); action endaction endmethod
endmodule
