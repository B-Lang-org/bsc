import Inout::*;
import Connectable::*;

import InoutStub::*;

(* synthesize *)
module mkFourInoutBuses#(Inout#(Int#(5)) a,
                         Inout#(Int#(5)) b,
                         Inout#(Int#(5)) c,
                         Inout#(Int#(5)) d,
                         Inout#(Int#(5)) e,
                         Inout#(Int#(5)) f)();

  mkConnection(e,f);
  Empty g <- mkInoutArgStub(f);
  mkConnection(d,f);

  InoutSrcStub h <- mkInoutStubSrc1();
  Empty i <- mkInoutArgStub(h.foo);
  InoutSrcStub j <- mkInoutStubSrc2();
  mkConnection(h.foo, j.foo);

  InoutSrcStub k <- mkInoutStubSrc2();
  mkConnection(a,k.foo);
  mkConnection(b,k.foo);

  InoutSrcStub l <- mkInoutStubSrc2();
  mkConnection(a,l.foo);
  Empty m <- mkInoutArgStub(a);

  InoutSrcStub n <- mkInoutStubSrc1();
  InoutSrcStub o <- mkInoutStubSrc1();
  InoutSrcStub p <- mkInoutStubSrc1();

  mkConnection(p.foo, c);
  mkConnection(n.foo, o.foo);
  mkConnection(o.foo, c);

  Empty q <- mkInoutArgStub(p.foo);

endmodule
