typedef union tagged {
    struct { Bit#(a) f1;
             b f2;
             union tagged {d ST1; Bit#(a) ST2; } f5;
           } T1;
    Bit#(c) T2;
} U#(numeric type a, type b, numeric type c, type d);

