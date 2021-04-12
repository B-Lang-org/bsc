typedef union tagged {
  Bit#(16) DataWidth;
} T1;

typedef 32 DataWidth;

function Integer getDataWidth();
   return DataWidth;
endfunction
