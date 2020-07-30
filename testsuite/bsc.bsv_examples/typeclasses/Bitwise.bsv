typedef Bit#(3) IdT;

typedef struct {
   IdT f3;
   IdT f2;
   IdT f1;
} AddrT deriving (Eq, Bits);

// some addresses which we will try to apply bitwise operators to
AddrT addr1 = AddrT { f3: 2, f2: 3, f1: 4 };
AddrT addr2 = AddrT { f3: 2, f2: 2, f1: 2 };


// Question: How do we perform bitwise "&" on two addresses?


// Option #1: Use the operator on the packed bit vectors
AddrT res1 = unpack( pack(addr1) & pack(addr2) );


// Option #2: Use the operator on the fields of the structs
//   This is works at the level of the struct.  If the struct had a
//   strange packing into bits, this could give different results.
function AddrT andAddr(AddrT in1, AddrT in2);
   return (AddrT { f3:  in1.f3  & in2.f3,
		   f2:  in1.f2  & in2.f2,
		   f1:  in1.f1  & in2.f1 });
endfunction

AddrT res2 = andAddr( addr1, addr2 );


// Option #3: Overload the bitwise operators for type AddrT
//   To do this, use the "instance" syntax described in the BSV
//   Reference Guide section 14.1.3, "Declarations of type class instances".
//   With this syntax, define an instance for the "Bitwise" type class,
//   whose functions are listed in section B.1 "Type Classes".

instance Bitwise #(AddrT);

  // use "\" to escape the operator for use as an identifier
  function AddrT \& (AddrT in1, AddrT in2);
     return (AddrT { f3:  in1.f3  & in2.f3,
		     f2:  in1.f2  & in2.f2,
		     f1:  in1.f1  & in2.f1 });
  endfunction

  // fill in the other operators here

endinstance

AddrT res3 = addr1 & addr2 ;

