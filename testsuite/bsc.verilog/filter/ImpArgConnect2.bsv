import Inout::*;
import Connectable::*;

import InoutStub::*;

(* synthesize *)
module mkImpArgConnect2#(Inout#(Int#(5)) arg)();

  InoutSrcStub a <- mkInoutStubSrc1;

  mkConnection(a.foo,arg);

endmodule


(* synthesize *)
module mkArgImpConnect2#(Inout#(Int#(5)) arg)();

  InoutSrcStub b <- mkInoutStubSrc2;

  mkConnection(arg, b.foo);

endmodule
