import Connectable::*;

(* synthesize *)
(* no_default_clock *)
module sysNoDefaultClock_Inout#(Inout#(Bool) io, Inout#(Bool) io2)();
  mkConnection(io,io2);
endmodule
