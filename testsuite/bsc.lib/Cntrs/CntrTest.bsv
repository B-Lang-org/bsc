import Cntrs::*;

import StmtFSM::*;


(*synthesize*)
module sysCntrTest();

   Count#(UInt#(4))  udut <- mkCount(0);
   Count#(Int#(4))   idut <- mkCount(0);
   Count#(Bit#(4))   bdut <- mkCount(0);

   Reg#(UInt#(5))   i <- mkReg(0);

   function Action incrAll (Integer v)  = (
      action
         udut.incr (fromInteger (v));
         idut.incr (fromInteger (v));
         bdut.incr (fromInteger (v));
      endaction);
   function Action decrAll (Integer v)  = (
      action
         udut.decr (fromInteger (v));
         idut.decr (fromInteger (v));
         bdut.decr (fromInteger (v));
      endaction);
   function Action updateAll (Integer v)  = (
      action
         udut.update (fromInteger (v));
         idut.update (fromInteger (v));
         bdut.update (fromInteger (v));
      endaction);
   
   function Action writeAll (Integer v)  = (
      action
         udut <= (fromInteger (v));
         idut <= (fromInteger (v));
         bdut <= (fromInteger (v));
      endaction);


   
   rule showState (True);
      $display ("bdut = %d, idut = %d, udut = %d", bdut, idut, udut);
   endrule
   
   let testSeq =
   (seq
       i <= 20;
       $display ("Incrementing by 1...........................");
       while (i != 0)
          action
             i <= i -1;
             incrAll(1);
          endaction
       i <= 20;
       $display ("Decrementing by 1...........................");
       writeAll(0);
       while (i != 0)
          action
             i <= i -1;
            decrAll(1);
          endaction
       $display ("Incr by 3 Decr by 1...........................");
       writeAll(0);
       i <= 20;
       while (i != 0)
          action
             i <= i -1;
            incrAll(3);
             decrAll(1);
          endaction
       $display ("Incr by 3 Decr by 1 update to 7 ...........................");
       writeAll(0);
       i <= 20;
       while (i != 0)
          action
             i <= i -1;
             incrAll(3);
             decrAll(1);
             updateAll(7);
          endaction
       $display ("Incr by 3 Decr by 1 update to 7 write to 4 ...........................");
       writeAll(0);
       i <= 20;
       while (i != 0)
          action
             i <= i -1;
             incrAll(3);
             decrAll(1);
             writeAll(4);
          endaction
    endseq);
   
   mkAutoFSM(testSeq);

endmodule
