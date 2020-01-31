package DefaultValue ;

// Default Value package
// This package provides a typeclass DefaultValue#(t).
// The idea of this typeclass is to provide an overloaded
// value, defaultValue (for defaultValue), for the type t.
//
// Uses:
// This should be useful for specifying initial or reset value for
// structures. E.g.
//   Reg#(Int#(17))               rint  <- mkReg#(defaultValue); // initial value 0
//   Reg#(Tuple2#(Bool,UInt#(5))) tbui  <- mkReg#(defaultValue); // value is(False,0)
//   Reg#(Vector#(n,Bool)         vbool <- mkReg(defaultValue)   //  initial value all False
//   Reg#(MyStruct)               mstr  <- mkReg(defaultValue);  // defined by user
// using this typeclass should replace the unsafe use of unpack. e.g.
//   Reg#(MyStruct)               mybad <- mkReg(unpack(0)); // Bad use of unpack
//
// Another use model is for module instantiation which require a large structure as
// as argument.
// ModParam modParams = defaultValue ; // generate default value
// modParams.field1 = 5 ;        // override some default values
// modParams.field2 = 1.4 ;      //
// ModIfc <- mkMod (modParams) ; // construct the module
//
//

import Vector :: *;

typeclass DefaultValue #( type t );
    t defaultValue ;
endtypeclass

// Any type in the Literal class can have a default value -- simply 0
// This picks up Bit#(n), Int#(n), UInt#(n), Real, Integer
// as well as FixedPoint, Complex
instance DefaultValue # (t)
   provisos (Literal#(t));
   defaultValue = fromInteger (0);
endinstance

// Allow Bools to have default value -- False in this case
instance DefaultValue #( Bool );
   defaultValue = False ;
endinstance

instance DefaultValue #(void);
   defaultValue = ?;
endinstance

// For Maybe, a default value is tagged Invalid
instance DefaultValue #( Maybe#(t) );
   defaultValue = tagged Invalid ;
endinstance


// Default values for tuples are just the default values of their member type
instance DefaultValue #( Tuple2#(a,b) )
   provisos (DefaultValue#(a)
             ,DefaultValue#(b) );
   defaultValue = tuple2 (defaultValue, defaultValue );
endinstance

// Since larger tuples are constructed from pairs, the above instance
// inductively covers all tuples.

// A default default value for a Vector replicates the element's default value
instance DefaultValue #( Vector#(n,t) )
   provisos (DefaultValue#(t));
   defaultValue = replicate (defaultValue) ;
endinstance

endpackage
