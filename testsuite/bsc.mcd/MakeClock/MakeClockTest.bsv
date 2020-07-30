
import Clocks::*;
import StmtFSM::*;

(* synthesize *)
module sysMakeClockTest();

   Clock clk <- exposeCurrentClock;
   MakeClockIfc#(Bit#(1)) mc <-  mkClock( 0, True );
   Clock cx = mc.new_clk;
   Reset rx <- mkAsyncResetFromCR( 0, mc.new_clk);
   //  register like probe
   Reg#(Bit#(2))  s <- mkReg(0);
   CrossingReg#(Bool) gotest <- mkNullCrossingReg(cx, False);

   SyncFIFOIfc#(UInt#(20))  sfifo <- mkSyncFIFOToCC (128, cx, rx );

   // Counter on the derived clock
   Reg#(UInt#(20)) cr <- mkRegA(0, clocked_by mc.new_clk, reset_by rx );
   rule inc (gotest.crossed);
      cr <= cr + 1;
      sfifo.enq(cr+1);
   endrule

   // Counter on the default clock
   Reg#(UInt#(20)) c <- mkReg(0);
   rule dis ;
      c <= c + 1;
   endrule
   rule examine ;
      sfifo.deq;
      $display ( "Ticks: %d %d", c, sfifo.first );
   endrule

   function Stmt change ( Bool gi, Bit#(1) ci, Bool go, Bit#(1) co );
   return (seq
              action
                 mc.setClockValue( 0 );
                 mc.setGateCond( False );
                 s <= {pack(gi), ci };
              endaction
              mc.setGateCond( gi );
              action
                 mc.setClockValue( ci );
                 s <= {pack(gi), ci };
              endaction
              action
                 mc.setGateCond( go );
                 mc.setClockValue( co );
                 s <= {pack(go), co };
              endaction
             noAction; noAction;
           endseq);
   endfunction

   Stmt test =
   (seq
      // noAction;
       // first 2 actions are to tick clock out of reset for sfifo and cr
       mc.setClockValue(1);
       mc.setClockValue(0);
       mc.setClockValue(1);
       action
          mc.setClockValue(0);
          gotest <= True ;
       endaction
       change( False, 0, False, 0);
       change( False, 0, False, 1);
       change( False, 0, True, 0);
       change( False, 0, True, 1);

       change( False, 1, False, 0);
       change( False, 1, False, 1);
       change( False, 1, True, 0);
       change( False, 1, True, 1);

       change( True, 0, False, 0);
       change( True, 0, False, 1);
       change( True, 0, True, 0);
       change( True, 0, True, 1);

       change( True, 1, False, 0);
       change( True, 1, False, 1);
       change( True, 1, True, 0);
       change( True, 1, True, 1);
    noAction;
    noAction;
    noAction;
    noAction;
    endseq );

   let fsm <- mkAutoFSM(test);

endmodule
