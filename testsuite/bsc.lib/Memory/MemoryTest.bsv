
import FIFOF::*;
import ClientServer::*;
import GetPut::*;
import Memory::*;
import Connectable::*;
import RegFile::*;
import StmtFSM::*;
import Vector::*;

(*synthesize*)
module sysMemoryTest(Empty);

   let dut <- mkTestMemory;

   RegFile#( Bit#(20), Bit#(256) ) rf <- mkRegFileFull;

   mkConnection (dut, rf);


endmodule

(*synthesize*)
module mkTestMemory ( MemoryClient#(32, 256) );

   FIFOF#(MemoryRequest#(32,256)) req_f <- mkFIFOF;
   function Action doWrite (Bit#(32) a, Bit#(256) d, Bit#(32) be);
   action
      req_f.enq ( MemoryRequest { write: True,
                                 address:a,
                                 data:d,
                                 byteen: be
         });
   endaction
   endfunction

   function Action doRead (Bit#(32) a, Bit#(32) be);
   action
      req_f.enq ( MemoryRequest { write: False,
                                 address:a,
                                 data:?,
                                 byteen: 0
         });
   endaction
   endfunction

   Reg#(Bit#(32))  da <- mkReg(0);
   Reg#(Bit#(256)) dd <- mkReg(0);
   Reg#(Bit#(32))  dbe <- mkReg('1);


   Bit#(256) dataIncr = pack (replicate(8'h1));

   Stmt readall =
   seq
      da <= 32;
      while (da != 0)
         action
            doRead(da,0);
            da <= da - 1;
         endaction
      delay(10);
   endseq;

   Stmt zeroMem =
   seq
      da <= 32;
      while (da != 0)
         action
            doWrite(da,0,'1);
            da <= da - 1;
         endaction
      delay(10);
   endseq;

   Stmt testseq =
   seq
      $display( "Initial memory contents");
      readall;

      da <= 32;
      while (da != 0)
         action
            doWrite(da, dd, dbe);
            da <= da - 1;
            dd <= dd + dataIncr;
         endaction
      $display( "Incr data");
      readall;
      zeroMem;


      dbe <= 'b1;
      while (dbe != '1) seq
         da <= 32;
         while (da != 0)
            action
               doWrite(da, dd, dbe);
               da <= da - 1;
               dd <= dd + dataIncr;
               dbe <= truncateLSB ({dbe,dbe} << 1);
            endaction
         $display( "Incr data and BE -- %h", dbe);
         readall;
         zeroMem;
         dbe <= ((dbe + 1) * (dbe + 1) ) -1;
      endseq
   endseq;

   mkAutoFSM (testseq);


   interface Get /* #(MemoryRequest#(32,256))*/ request = toGet(req_f);
   interface Put /* #(MemoryResponse#(32,256))*/ response;
      method Action put (MemoryResponse#(256) x);
         $display (fshow(x));
      endmethod
   endinterface

endmodule
