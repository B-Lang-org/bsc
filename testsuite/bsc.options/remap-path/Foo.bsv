package Foo;

interface Counter;
   method Action bump();
   method Bit#(8) value();
endinterface

(* synthesize *)
module mkFoo(Counter);
   Reg#(Bit#(8)) count <- mkReg(0);

   method Action bump();
      count <= count + 1;
   endmethod

   method Bit#(8) value();
      return count;
   endmethod
endmodule

endpackage
