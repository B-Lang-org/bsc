import FIFO :: *;
import GetPut :: *;
import Connectable :: *;

(* synthesize *)
module sysTest1 ();
   Empty sub1 <- mkSub1;

   rule r0;
      $display("r0");
   endrule
endmodule

module mkSub1();
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   mkConnection(toGet(f1), toPut(f2));

   (* hide_all *)
   Empty sub2 <- mkSub2;

   rule r1;
      $display("r1");
   endrule
endmodule

module mkSub2();
   Empty sub3 <- mkSub3;

   rule r2;
      $display("r2");
   endrule
endmodule

module mkSub3();
  rule r3;
     $display("Hi");
  endrule
endmodule

