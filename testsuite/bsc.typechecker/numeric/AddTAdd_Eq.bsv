
// A struct with two type parameters
typedef struct {
  Bit#(n) f1;
  Bit#(m) f2;
} T#(type n, type m) deriving(Eq, Bits);

// a sub-function which has required provisos
function Bit#(n) fnSub(T#(x,y) v)
 provisos (Add#(n, junk, TAdd#(n,junk)),
           Bits#(T#(x,y), TAdd#(n,junk)));
   return truncate(pack(v));
endfunction

// a function which calls the sub-function and also has provisos
function Bit#(n) fnTop(T#(x,y) v)
 provisos (Add#(n, junk, TAdd#(n,junk)),
           Bits#(T#(x,y), TAdd#(n,junk)));
     return fnSub(v);
endfunction

