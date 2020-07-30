module mkFoo(Reg #(a)) provisos (Bits#(a,sa), Arith#(a));
    method a _read(); return ?; endmethod
    method Action _write(a val); action endaction endmethod
endmodule
