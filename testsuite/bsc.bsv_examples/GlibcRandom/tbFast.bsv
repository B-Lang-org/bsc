package tbFast;
import StmtFSM::*;
import GetPut::*;
import ClientServer::*;
import GlibcRandom::*;

(*synthesize*)
// (*mutually_exclusive="actionof_l13c20,myrand.lc.lc"*) (*mutually_exclusive="actionof_l13c20_1,myrand.lc.lc"*)  (*mutually_exclusive="actionof_l16c7,myrand.lc.lc"*)
module systbFast();
   Server#(int,int) myrand<-mkRandom;
   mkAutoFSM(seq
      myrand.request.put(1);
      repeat(10000)(action
         int result<-myrand.response.get;
         endaction);
      action
         int result<-myrand.response.get;
         $display(result);
      endaction
      endseq);
endmodule

endpackage
