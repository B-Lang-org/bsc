package Priority;

// First comes a utility function which returns True if any bits in the
// argument are 1.  (Note that we have not bothered to set up a tree of OR
// operations, partly because the tool's Boolean optimisation features would
// probably flatten the expression again, and partly because this optimisation
// can safely be left to the netlist synthesis tool.)

function Bool any1(Bit#(sa) bs) = (bs!=0);

// The new type Priority is a one-field structure.  The numeric-type argument
// mp is the maximum priority we wish to handle.  We intend to use a unary
// representation: for priority n, the n bits [n-1:0] will be 1.

typedef struct {Bit#(mp) p;} Priority#(type mp) deriving (Bits, Eq);

// The Literals are the class of types whose values can be specified by
// numerical literal constants in the source text.  The compiler turns the
// literal constant into an Integer; so in order to declare a type to be in
// the Literal class we must define the fromInteger function, to convert that
// integer to the required representation (in this case the unary encoding).

instance Literal#(Priority#(mp));
   function fromInteger(n);
      let maxp = valueOf(mp);
      if (n>maxp) return (error("attempt to make priority greater than maximum"));
      else return (Priority {p: ((0-1) >> (fromInteger(maxp - n)))});
   endfunction
endinstance

// The advantage of the unary representation is an efficient algorithm for the
// "<" test.  The other comparison operations are defined in terms of this.

instance Ord#(Priority#(mp));
   function \< (p1,p2);
      let b1 = p1.p;
      let b2 = p2.p;
      return (any1(b2 & (invert(b1))));
   endfunction
   function \>  (p1,p2) =  (p2 < p1);
   function \<= (p1,p2) = !(p1 > p2);
   function \>= (p1,p2) = !(p1 < p2);
      endinstance

// For purposes of displaying test-bench output it is convenient to have a
// function to convert a priority to the standard representation.  There are
// many less naive implementations of this than the one given here, but there
// is no need for this function to be efficient!

function UInt#(si) priority2uint(Priority#(mp) pr)
   provisos(Add#(mp,1,k),Log#(k,si));
   let maxp = fromInteger(valueOf(mp));
   UInt#(si) n = 0;
   for (Nat i=0; i<maxp; i=i+1)
      if (pr.p[i]==1) n=n+1;
   return n;
endfunction

endpackage
