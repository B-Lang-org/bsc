typedef struct { Bool foo; } Bar;

interface Confusing;
  method Bit#(1) breakIt(Nat x);
  method Bit#(1) fixIt(Nat x);
endinterface


module mkTest (Confusing);

  Bar x = Bar { foo: True };

  method breakIt(x);
    return x[0];
  endmethod

/*
  method Bit#(1) fixIt(Nat x);
    return x[0];
  endmethod
*/
endmodule
