// Test that SizeOf in the base type of an instance (not just its provisos)
// is expanded, when it's hidden inside a type synonym

module sysExpSizeOf_InstancesBaseSyn ();
   S r = ?;
   T x = cfn(r);
endmodule

// -------------------------

typeclass C#(type a, numeric type m);
   function Bit#(m) cfn(a value);
endtypeclass

typedef Bit#(12) T;

typedef SizeOf#(T) ST;

typedef struct{
   Bool f1;
   Bool f2;
} S deriving (Bits, Eq);

// SizeOf is not immediately visible unless ST is expanded
instance C#(S, ST);
   function cfn(b) = 0;
endinstance

// -------------------------

