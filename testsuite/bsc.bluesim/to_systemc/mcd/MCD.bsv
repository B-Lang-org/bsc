import Clocks::*;

interface Switch#(type t);
  method Action enq_a(t x); // clock a
  method Action enq_b(t x); // clock b
  method Action deq();      // clock out
  method t first();         // clock out
  method Action flip();     // default clock
endinterface

(* synthesize *)
module mkMCD(Clock clk_a, Reset rstn_a, Clock clk_b, Reset rstn_b, 
	     Clock clk_out, Switch#(Bit#(32)) ifc);
  
  Reg#(Bool) switch();
  mkReg#(False) the_switch(switch);

  SyncFIFOIfc#(Bit#(32)) a_sync <- mkSyncFIFOToCC(2, clk_a, rstn_a);
  SyncFIFOIfc#(Bit#(32)) b_sync <- mkSyncFIFOToCC(2, clk_b, rstn_b);
  SyncFIFOIfc#(Bit#(32)) out_sync <- mkSyncFIFOFromCC(2, clk_out);

  rule push_a(switch);
    out_sync.enq(a_sync.first);
    $display( "%0t: moving %0x from a", $time(), a_sync.first ) ;
    a_sync.deq;
  endrule

  rule push_b(!switch);
    out_sync.enq(b_sync.first);
    $display( "%0t: moving %0x from b", $time(), b_sync.first ) ;
    b_sync.deq;
  endrule

  method enq_a = a_sync.enq;
  method enq_b = b_sync.enq;
  method deq   = out_sync.deq;
  method first = out_sync.first;

  method Action flip();
     switch <= !switch;
  endmethod

endmodule
