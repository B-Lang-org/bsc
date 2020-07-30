// Test that SizeOf in the base type of an instance (not just its provisos)
// is expanded

module sysExpSizeOf_InstancesBase ();
   S r = ?;
   T x = cfn(r);
endmodule

// -------------------------

typeclass C#(type a, numeric type m);
   function Bit#(m) cfn(a value);
endtypeclass

typedef Bit#(12) T;

typedef struct{
   Bool f1;
   Bool f2;
} S deriving (Bits, Eq);

instance C#(S, SizeOf#(T));
   function cfn(b) = 0;
endinstance

// -------------------------

