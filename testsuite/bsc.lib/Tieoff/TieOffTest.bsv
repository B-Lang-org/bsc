
import TieOff:: *;
import GetPut :: *;
import FIFO ::*;
import FShow::*;

import StmtFSM::*;

instance TieOff #(Get #(t) )
   provisos( FShow#(t) ) ;
   module mkTieOff ( Get#(t) ifc, Empty inf);
      rule getSink (True);
         t val <- ifc.get;
         $display("Value from get interface is: ", fshow(val));
      endrule
   endmodule
endinstance



instance TieOff #(Get #(Bool) );
   module mkTieOff ( Get#(Bool) ifc, Empty inf);
      rule getSink (True);
         Bool val <- ifc.get;
         $display("Boolean Value from get interface is: ", fshow(val));
      endrule
   endmodule
endinstance



(*synthesize*)
module sysTieOffTest ();
   
   FIFO#(Int#(15)) fi <- mkFIFO ;
   mkTieOff(toGet(fi));

   FIFO#(Bool) fb <- mkFIFO ;
   mkTieOff(toGet(fb));
   
   let ts = 
   (seq
       fi.enq(10);
       fi.enq(11);
       fb.enq(False);
       noAction;
    endseq);
   
   mkAutoFSM(ts);
   
   
endmodule
