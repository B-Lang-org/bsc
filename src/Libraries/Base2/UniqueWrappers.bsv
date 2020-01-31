package UniqueWrappers;

/*
Sometimes it is desired to use a piece of logic at several places in a design,
but it is too bulky or otherwise expensive to duplicate at each site.
Sometimes the right thing to do is to make the piece of logic into a
separately synthesized module -- then, if this module is instantiated only
once, it will not be duplicated, and the tool will automatically generate the
scheduling and multiplexing logic to share it among the sites which use its
methods.  Sometimes, however, this is not convenient.  One reason might be
that the logic is to be incorporated into a sub-module of the design which is
itself polymorphic -- this will probably cause difficulties in observing the
constraints necessary for a module which is to be separately synthesized.  And
if a module is *not* separately synthesized, the tool will inline its logic
freely wherever it is used, and thus duplication will not be prevented as
desired.

This package covers the case where the logic to be shared is combinational.
It may be thought of as surrounding this combinational function with a
protective shell (a "unique wrapper") which will prevent its duplication.  The
module mkUniqueWrapper takes a one-argument function as a parameter; both the
argument type a and the result type b must be representable as bits (that is,
they must both be in the Bits typeclass).  It provides an interface with one
actionvalue method, func, which takes an argument of type a and produces an
actionvalue of type ActionValue#(b).  If the module is instantiated only once,
the logic implementing its parameter will be instantiated just once; the
module's method may, however, be used freely at several places.

It might be wondered why the method is an actionvalue: after all, actionvalues
usually involve side-effects, and the logic of the parameter function is
purely combinational.  But claiming, and then releasing, a unique resource is
a form of side-effect, albeit a temporary one.  Another way of looking at it
is to observe that actionvalue methods have ENABLE signals; and such a signal
is needed by the tool for organizing the scheduling and multiplexing between
the calling sites.

The type of the Wrapper interface is as follows.
*/

interface Wrapper#(type a, type b);
   method ActionValue#(b) func (a x);
endinterface

/*
The header of the mkUniqueWrapper module is as follows.
*/

module mkUniqueWrapper#(function b f(a x))(Wrapper#(a,b))
   provisos (Bits#(a,sa), Bits#(b,sb));

   RWire#(a) arg <- mkUnsafeRWire;
   RWire#(b) res <- mkUnsafeRWire;

   method ActionValue#(b) func (a x);
      arg.wset(x);
      let a = validValue(arg.wget);
      res.wset( f(a) );
      return (validValue(res.wget));
   endmethod
endmodule

/*
Variants of Wrapper and mkUniqueWrapper are also provided for coping with
parameter functions of two or three arguments; the interfaces have one and two
extra type parameters respectively.  In each case the result type is the final
parameter, following however many argument type parameters are required.

Note that if a function has more than three arguments, it can always be
rewritten or wrapped as one which takes the arguments as a single tuple; thus
the one-argument version mkUniqueWrapper can be used with this function.
*/

interface Wrapper2#(type a1, type a2, type b);
   method ActionValue#(b) func (a1 x, a2 y);
endinterface

module mkUniqueWrapper2#(function b f(a1 x, a2 y))(Wrapper2#(a1,a2,b))
   provisos (Bits#(a1,sa1), Bits#(a2,sa2), Bits#(b,sb));
   function ff(a);
      match {.x, .y} = a;
      return f(x,y);
   endfunction

   Wrapper#(Tuple2#(a1,a2), b) _m <- mkUniqueWrapper(ff);

   method ActionValue#(b) func(a1 x, a2 y);
      let r <- _m.func(tuple2(x,y));
      return r;
   endmethod
endmodule

interface Wrapper3#(type a1, type a2, type a3, type b);
   method ActionValue#(b) func (a1 x, a2 y, a3 z);
endinterface

module mkUniqueWrapper3#(function b f(a1 x, a2 y, a3 z))(Wrapper3#(a1,a2,a3,b))
   provisos (Bits#(a1,sa1), Bits#(a2,sa2), Bits#(a3,sa3), Bits#(b,sb));
   function ff(a);
      match {.x, .y, .z} = a;
      return f(x,y,z);
   endfunction

   Wrapper#(Tuple3#(a1,a2,a3), b) _m <- mkUniqueWrapper(ff);

   method ActionValue#(b) func(a1 x, a2 y, a3 z);
      let r <- _m.func(tuple3(x,y,z));
      return r;
   endmethod
endmodule

endpackage
