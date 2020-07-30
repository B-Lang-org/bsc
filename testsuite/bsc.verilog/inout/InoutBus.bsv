import Inout::*;
import Connectable::*;

import InoutStub::*;

(* synthesize *)
module mkInoutBus1#(Inout#(Int#(5)) c, Inout#(Int#(5)) d)();

  InoutSrcStub a <- mkInoutStubSrc1;
  InoutSrcStub b <- mkInoutStubSrc2;

  mkConnection(a.foo,b.foo);
  mkConnection(c,d);

  Empty e <- mkInoutArgStub(d);

  mkConnection(b.foo,d);

endmodule

(* synthesize *)
module mkInoutBus2#(Inout#(Int#(5)) a, Inout#(Int#(5)) b)();

  InoutSrcStub c <- mkInoutStubSrc1;
  InoutSrcStub d <- mkInoutStubSrc2;

  mkConnection(a,c.foo);
  mkConnection(b,d.foo);

  Empty e <- mkInoutArgStub(c.foo);

  mkConnection(a,b);

endmodule