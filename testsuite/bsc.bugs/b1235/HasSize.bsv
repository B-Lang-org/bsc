package HasSize;

typeclass HasSize#(type a, type b) provisos (Literal#(b)) dependencies (a determines b);
   function b size(a x);
endtypeclass
   
instance HasSize#(Array#(t), int);
   function int size(Array#(t) x) = fromInteger(arrayLength(x));
endinstance
				       
instance HasSize#(Bit#(n), s) provisos (Literal#(s));
   function s size(Bit#(n) x) = fromInteger(valueof(n));
endinstance

endpackage
