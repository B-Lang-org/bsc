import Inout::*;
import Connectable::*;

import InoutStub::*;

(* synthesize *)
module mkImpImpConnect1();

  InoutSrcStub a <- mkInoutStubSrc1;
  InoutSrcStub b <- mkInoutStubSrc2;

  mkConnection(a.foo,b.foo);

  Empty c <- mkInoutArgStub(a.foo);

endmodule


(* synthesize *)
module mkImpImpConnect2();

  InoutSrcStub a <- mkInoutStubSrc1;
  InoutSrcStub b <- mkInoutStubSrc2;

  mkConnection(b.foo,a.foo);

  Empty c <- mkInoutArgStub(a.foo);
endmodule
