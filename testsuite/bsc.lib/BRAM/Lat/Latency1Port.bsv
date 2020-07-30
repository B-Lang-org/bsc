import BRAM :: *;
import StmtFSM :: *;
import FIFOF :: *;
import ClientServer ::*;
import GetPut :: *;
import DefaultValue :: *;

typedef UInt#(10)  ADDR ;
typedef Bit#(10)    DATA ;


module mkLatency1Port ( BRAM_Configure cfg, Empty ifc);

   BRAM1Port# (ADDR, DATA) bram <- mkBRAM1Server(cfg);

   Reg#(UInt#(10))  cyc <- mkReg(0);


   FIFOF#(ADDR) readaddrF <- mkSizedFIFOF(20);


   function Action bramwrite (ADDR a, DATA d);
   action
      bram.portA.request.put ( BRAMRequest { write:True, address:a, datain:d, responseOnWrite:False } );
   endaction
   endfunction
   function Action bramread (ADDR a);
   action
      bram.portA.request.put ( BRAMRequest { write:False, address:a, datain:0, responseOnWrite:True } );
      $display ( "%d ReadRequest:  Address: %h", cyc, a);
      readaddrF.enq(a);
   endaction
   endfunction

   Reg#(UInt#(8)) delayCnt <- mkReg(0);
   rule delay (delayCnt != 0);
      delayCnt <= delayCnt - 1;
   endrule

   //When the delay count is 0, we can deq
   rule getreadresult (delayCnt == 0) ;
      readaddrF.deq;
      let a = readaddrF.first ;
      let d <- bram.portA.response.get;

      $display ( "%d Read result from %d --> %d", cyc, a, d );
      if (pack(a) != d )
         $display( "ERROR ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^" );
   endrule

   rule incrcyc (True);
      cyc <= cyc + 1 ;
   endrule

   Reg#(ADDR) cnt <- mkReg(0);

   Stmt initialize =
   (seq
       $display ("BRAM configuration: Latency: %d,  fifoDepth %d", cfg.latency, cfg.outFIFODepth) ;
       cnt <= 0;
       while (cnt != maxBound) seq
          action
             bramwrite (cnt, pack(cnt));
             cnt <= cnt  + 1;
          endaction
       endseq
       cnt <= 0 ;
    endseq);

   Action readAction =
   (action
       bramread (cnt);
       cnt <= cnt + 1 ;
    endaction);

   Stmt testseq =
   (seq
       initialize ;
       action cyc <= 0; $display ("1 read"); endaction
       // 4 reads
       delayCnt <= 0;
       readAction;
       delay (10);
       action cyc <= 0; $display ("2 read"); endaction
       readAction;
       readAction;
       delay (10);
       action cyc <= 0; $display ("3 read"); endaction
       readAction;
       readAction;
       readAction;
       delay (10);
       action cyc <= 0; $display ("4 read"); endaction

       readAction;
       readAction;
       readAction;
       readAction;
       delay (10);

       // 4 reads
       cnt <= 30;
       action cyc <= 0; $display ("4 reads, with delayed reads of 2"); endaction
       delayCnt <= 2;
       readAction;
       readAction;
       readAction;
       readAction;
       delay (10);

       // 4 reads
       cnt <= 40;
       action cyc <= 0; $display ("4 reads, with delay of 10 "); endaction
       delayCnt <= 10;
       readAction;
       readAction;
       readAction;
       readAction;
       delay (10);

       // 4 more reads no delay
       cnt <= 50;
       action cyc <= 0; $display ("4 reads, with delay of ZERO "); endaction
       readAction;
       readAction;
       readAction;
       readAction;
       delay (10);

       // 5 reads with delay with depth=4 last should stall.
       cnt <= 40;
       action cyc <= 0; $display ("5 reads, with delay of 10 "); endaction
       delayCnt <= 10;
       readAction;
       readAction;
       readAction;
       readAction;
       readAction;
       delay (10);

    endseq);

   mkAutoFSM(testseq);
endmodule
