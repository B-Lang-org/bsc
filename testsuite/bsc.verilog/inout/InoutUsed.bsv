import SenderReceiver::*;

import "BVI" InoutToVal =
module mkInoutToVal#(Inout#(int) arg)(ReadOnly#(int));
   inout IN = arg;
   default_clock clk(CLK);
   no_reset;
   method OUT _read();
   schedule _read CF _read;
endmodule

(* options="-remove-unused-modules" *)
(* synthesize *)
module sysInoutUsed();

  SingletonInout sender <- mkSender(96);

  ReadOnly#(int) val <- mkInoutToVal(sender.iioo);

  rule test;
    $display("Val %0d", val);
    $finish(0);
  endrule

endmodule
