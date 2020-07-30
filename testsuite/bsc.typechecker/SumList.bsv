import Vector::*;
      
// sumList with one proviso                                                      
function Bit#(n) sumList(Vector#(l, Bit#(m)) theInput) provisos (Add#(m,q,n)); 
      Vector#(l, Bit#(n)) extended; 
      extended = map(zeroExtend,theInput);
      return (foldr(add,0,extended));
endfunction: sumList 

// try the other order to test commutativity                                                            
function Bit#(n) sumList2(Vector#(l, Bit#(m)) theInput) provisos (Add#(q,m,n)); 
      Vector#(l, Bit#(n)) extended; 
      extended = map(zeroExtend,theInput);
      return (foldr(add,0,extended));
endfunction: sumList2 
