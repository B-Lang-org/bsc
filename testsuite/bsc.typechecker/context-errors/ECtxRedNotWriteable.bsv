interface EmptyWrite#(type a);
   method Action _write(a v);
endinterface

module mkEmptyWrite(EmptyWrite#(a));
   method Action _write(v);
      noAction;
   endmethod
endmodule

module test();
   
   EmptyWrite#(Bool) x <- mkEmptyWrite;
   
   rule test;
      x[0] <= True;
   endrule
   
endmodule


