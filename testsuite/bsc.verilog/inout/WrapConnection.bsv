import Connectable::*;

(*synthesize*)
module wrapConnection#(Inout#(int) recv, Inout#(int) send)();
      mkConnection(recv, send);  //flip me
endmodule: wrapConnection
