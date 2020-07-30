import Inout::*;
import Connectable::*;

import InoutStub::*;

(* synthesize *)
module mkImpArgConnect#(Inout#(Int#(5)) arg)();

  InoutSrcStub a <- mkInoutStubSrc1;

  mkConnection(a.foo,arg);

endmodule


(* synthesize *)
module mkArgImpConnect#(Inout#(Int#(5)) arg)();

  InoutSrcStub b <- mkInoutStubSrc2;

  mkConnection(arg, b.foo);

endmodule
