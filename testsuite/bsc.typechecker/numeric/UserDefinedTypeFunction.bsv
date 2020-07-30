// This is an example demonstrating the kind of ad-hoc mapping between
// high- and low-level views of parameterized interfaces that Shep
// requested.
//
// In this example, the top-level interface is parameterized over a
// single number n, which must be prime.  The low-level interface has
// 2 parameters: the index of the prime number in the list of primes
// and the count of characters in the english spelling of the prime
// number.  These were chosen to demonstrate the ability to encode
// non-linear mappings.

// Interface defined with multiple parameters
interface MyLowLevelIfc#(numeric type prime, numeric type chars);
   method ActionValue#(Bit#(prime)) meth(UInt#(chars) x);
endinterface: MyLowLevelIfc

// A type class and instances defining the high-to-low-level mapping
typeclass MyIfcTable#(numeric type n, numeric type p, numeric type c)
   dependencies(n determines(p,c));
endtypeclass: MyIfcTable

instance MyIfcTable#(2,1,3);  endinstance // two    ==> 1st prime, has 3 characters
instance MyIfcTable#(3,2,5);  endinstance // three  ==> 2nd prime, has 5 characters
instance MyIfcTable#(5,3,4);  endinstance // five   ==> 3rd prime, has 4 characters
instance MyIfcTable#(7,4,5);  endinstance // seven  ==> 4th prime, has 5 characters
instance MyIfcTable#(11,5,6); endinstance // eleven ==> 5th prime, has 6 characters

// ======================== BEGIN KLUDGE ========================

// This code should really be isolated in its own file, with lots of
// warnings, indented 6 feet down and covered with dirt.

// There is only one way other than the numeric type classes (TAdd,
// etc.)  to create a type-level function returning a numeric type:
// the SizeOf pseudo-function applied to a type with a Bits instance.
// This code abuses that facility to deconstruct types.

// never attempt to create one of these structures, please!
// it's only purpose is to convey type information.
typedef struct { Bit#(n) x; Bit#(i) y; } ExtractParam#(numeric type n, numeric type i);

instance Bits#(ExtractParam#(n,1),p) provisos(MyIfcTable#(n,p,c));
   function Bit#(p) pack(ExtractParam#(n,1) x)   = error("Never call this!");
   function ExtractParam#(n,1) unpack(Bit#(p) x) = error("Never call this!");
endinstance

instance Bits#(ExtractParam#(n,2),c) provisos(MyIfcTable#(n,p,c));
   function Bit#(c) pack(ExtractParam#(n,2) x)   = error("Never call this!");
   function ExtractParam#(n,2) unpack(Bit#(c) x) = error("Never call this!");
endinstance

// A nicer interface that hides the kludgy bits
typedef SizeOf#(ExtractParam#(n,1)) GetP#(numeric type n);
typedef SizeOf#(ExtractParam#(n,2)) GetC#(numeric type n);

// ======================== END KLUDGE ========================

// Define a high-level view of the interface based on a single parameter
typedef MyLowLevelIfc#(GetP#(n),GetC#(n)) MyIfc#(numeric type n);

// Higher-level module uses the higher-level interface
interface TopIfc#(numeric type n);
   interface MyIfc#(n) sub;
endinterface

// Parameterized, non-synthesizable module implementing
// the
module mkTop(TopIfc#(n))
   provisos(MyIfcTable#(n,p,c)); // extract low-level types from the table
// alternative style: provisos(NumAlias#(p,GetP#(n)), NumAlias#(c,GetC#(n)));

   Reg#(UInt#(c)) counter <- mkReg(0);

   interface MyIfc sub;
      method ActionValue#(Bit#(p)) meth(UInt#(c) x);
	 counter <= counter + x;
	 Bit#(p) zeros = '0;
	 return truncate({zeros,pack(counter)});
      endmethod
   endinterface
endmodule

// Add a synthesis boundary specialized for the prime number 5
(* synthesize *)
module mkTopSynth(TopIfc#(5));
   let _ifc <- mkTop();
   return _ifc;
endmodule
