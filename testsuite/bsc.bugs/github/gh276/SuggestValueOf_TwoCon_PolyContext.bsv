typedef union tagged {
  Bit#(16) DataWidth;
} T1;

typedef union tagged {
  Bit#(8) DataWidth;
} T2;

typedef 32 DataWidth;

function Bool is64 (Integer x);
   // The expected type for DataWidth is a variable because '==' is overloaded
   return (DataWidth == 64);
endfunction
