package DummyDriver ;

import Vector::*;

// DummyDriver package
// This package provides a typeclass DummyDriver#(t)
// which is used to provide a dummy stub supplying some interface.

// Example -- a dummy driver for a Get interface.
// This is a module which provides a Get interface that is
// never ready.
//
// instance DummyDriver#(Get#(t)) provisos(Bits#(t,st));
//    module mkStub(Get#(t) ifc);
//      method ActionValue#(t) get() if (False);
//        return ?;
//      endmethod
//    endmodule
// endinstance

typeclass DummyDriver#(type i);
  module mkStub(i ifc);
endtypeclass

instance DummyDriver#(Vector#(n,i))
   provisos (DummyDriver#(i));
   module mkStub(Vector#(n,i) ifc);
      Vector#(n,i) _vifc <- replicateM(mkStub);
      return _vifc;
   endmodule
endinstance

endpackage: DummyDriver
