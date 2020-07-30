interface Foo#(type a);
   method Action write(a x);
endinterface

interface Bar#(type a);
   method Action write(a x);
   method a read();
endinterface

module mkTest ();
   function f(ifc);
      ifc.write = constFn(noAction);
      return ifc;
   endfunction
endmodule

