import Inout::*;
import Connectable::*;

import InoutStub::*;

(* synthesize *)
module mkTwoInoutBuses#(Inout#(Int#(5)) a,
                        Inout#(Int#(5)) b,
                        Inout#(Int#(5)) c,
                        Inout#(Int#(5)) d)();

  InoutSrcStub e <- mkInoutStubSrc1;
  InoutSrcStub f <- mkInoutStubSrc1;
  InoutSrcStub g <- mkInoutStubSrc2;
  InoutSrcStub h <- mkInoutStubSrc2;

  mkConnection(e.foo,f.foo);
  mkConnection(a,e.foo);
  mkConnection(b,f.foo);
  mkConnection(c,f.foo);

  mkConnection(g.foo,d);
  mkConnection(h.foo,d);

  Empty i <- mkInoutArgStub(g.foo);
  Empty j <- mkInoutArgStub(d);
  Empty k <- mkInoutArgStub(e.foo);

endmodule
