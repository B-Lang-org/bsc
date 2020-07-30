typeclass C#(type x) provisos(Literal#(x));
   module cmod (Reg#(x));
      // This generates a Cstruct CSyntax expression
      method _read = 0;
      method _write(val) = noAction;
   endmodule
endtypeclass

instance C#(Bit#(8));
endinstance

