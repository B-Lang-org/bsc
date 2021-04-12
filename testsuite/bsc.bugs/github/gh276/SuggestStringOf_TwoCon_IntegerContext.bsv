typedef union tagged {
  Bit#(16) DataWidth;
} T1;

typedef union tagged {
  Bit#(8) DataWidth;
} T2;

typedef "Foo" Name;

function String getName();
   return Name;
endfunction
