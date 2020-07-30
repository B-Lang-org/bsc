interface Foo#(type a);
   method Action write(a x);
endinterface

interface Bar#(type a);
   method Action write(a x);
endinterface

interface Baz#(type a);
   method a read();
endinterface


module mkTest ();
   function f(ifc);
      return ifc.write(True);
   endfunction
endmodule

