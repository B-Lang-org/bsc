
// A struct with two type parameters
typedef struct {
  Bit#(n) f1;
  Bit#(m) f2;
} T#(type n, type m);

instance Bits#(T#(n,m), sz) provisos (Mul#(n,m,sz));
   function pack(x) = ?;
   function unpack(x) = ?;
endinstance

// a sub-function which has required provisos
function Bit#(n) fnSub(T#(x,y) v)
 provisos (Mul#(n, junk, TMul#(n,junk)),
           Bits#(T#(x,y), TMul#(n,junk)));
   return ?;
endfunction

// a function which calls the sub-function and also has provisos
function Bit#(n) fnTop(T#(x,y) v)
 provisos (Mul#(n, junk, TMul#(n,junk)),
           Bits#(T#(x,y), TMul#(n,junk)));
     return fnSub(v);
endfunction

