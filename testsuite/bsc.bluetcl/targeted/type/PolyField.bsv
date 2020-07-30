interface I1;
   method Action set (t value, Reg#(t) rg);
endinterface

interface I2;
   method t id(t x);
endinterface

interface I3#(type a);
   method Action set (a dummy, t value, Reg#(t) rg);
endinterface

interface I4#(type a);
   method t id(t x, a dummy);
endinterface


typedef struct {
  function t f(t x) id;
} S1;

typedef struct {
  function t f(t x, b y) id;
} S2#(type b);

