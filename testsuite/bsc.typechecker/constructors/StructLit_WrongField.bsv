typedef struct { Bit#(2) field1; } S1 ;
typedef struct { Bit#(2) field2; } S2 ;

function S1 f();
   return (S1 { field2: 0 });
endfunction

