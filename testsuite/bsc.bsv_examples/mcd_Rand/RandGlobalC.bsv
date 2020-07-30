import Connectable::*;
import GetPut::*;
import CGetPut::*;

// This file contains a few definitions required by all the packages in the
// system.  We define the interface which the clients will use to export
// information to the outside world.

interface Component2;
  method Bit#(6) value;
endinterface

// Both the generator and the users have interfaces which are themselves pairs
// of interfaces.  A pair of interfaces is indeed an interface itself, but it
// is defined as a pair rather than with an interface definition, as follows:

typedef Tuple2#(CGet#(4,Bit#(6)),CGet#(4,Bit#(6))) GenPair;
typedef Tuple2#(CPut#(4,Bit#(6)), Component2) UserIfc;

