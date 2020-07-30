typedef struct { Bit#(2) field1; } S1 ;
typedef struct { Bit#(2) field2; } S2 ;

function S1 f();
   S1 x;
   x.field2 = 0;
   return x;
endfunction

