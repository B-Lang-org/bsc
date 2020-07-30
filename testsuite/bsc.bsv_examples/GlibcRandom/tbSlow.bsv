package tbSlow;
import GlibcRandom::*;
import StmtFSM::*;
import GetPut::*;
(*synthesize*)
module systbSlow();
   Reg#(Randtable) randtable<-mkReg(srand(1));
   Get#(int) r<-mkRandomR(randtable);
   mkAutoFSM(seq
      repeat(10000)(action
	 int result<-r.get;
	 endaction);
            action
         int result<-r.get;
         $display(result); //89057537
      endaction
      endseq);

endmodule

endpackage
