package GlibcRandom;
import StmtFSM::*;
import Vector::*;
import GetPut::*;
import ClientServer::*;

// (*mutually_exclusive="lc.lc,initialize.actionof_l15c40"*) (*mutually_exclusive="lc.lc,initialize.actionof_l15c40_1"*)
module mkRandom(Server#(int,int));
   Reg#(Randtable) randtable<-mkRegU;
   LinearCongruential lc<-mkLinearCongruential(randtable);
   Get#(int) inner <-mkRandomR(randtable);
   Reg#(Bool)ready<-mkReg(False);
   FSM initialize<-mkFSMWithPred(seq
      lc.finished;
      repeat(fromInteger(numToDiscard))(action
         int result<-inner.get;
         endaction);
      ready<=True;
      endseq,!ready );
   //NOTE: put should only be called once ever.  It does not work to re-seed a RNG.  Maybe a future task.
   interface Put request;
      method Action put(int seed) if (!ready);
         lc.seed(seed);
         initialize.start;
      endmethod
   endinterface
   interface Get response;
      method ActionValue#(int) get if(ready) =inner.get;
   endinterface
   
endmodule

typedef 31 DEG_3;
Integer sEP_3=3;
Bit#(5) finalIndex=fromInteger(valueof(DEG_3)-1);
typedef Bit#(5) Index;

function Tuple2#(int,Randtable) fibonacci(Randtable v);
   int val=v[0]+v[sEP_3];
   v[sEP_3]=val;
   return tuple2(val,(rotate(v)));
endfunction

module mkRandomR#(Reg#(Randtable) randtable)(Get#(int));
   method ActionValue#(int) get;
      Tuple2#(int,Randtable) rv=fibonacci(randtable);
      randtable<=tpl_2(rv);
      Bit#(32) bval=pack(tpl_1(rv));
      Bit#(31) bvc=bval[31:1];
      Bit#(32) zbv={0,bvc};
      int result=unpack(zbv);
      return result;
   endmethod
endmodule

typedef Vector#(DEG_3,int) Randtable;


Integer numToDiscard=310;

//this takes 300000 elaboration steps.
function Randtable discardInitial(Randtable r);
   for(Integer i=0;i<numToDiscard;i=i+1)
      r=tpl_2(fibonacci(r));
   return r;
endfunction

function Randtable srand(int seed);
   return discardInitial(lcong(seed));
endfunction

interface LinearCongruential;
   method Action seed(int inSeed);
   method Action finished;
endinterface

function int getnewword(int word);
   int hi=word/127773;
   int lo=word%127773;
   int newword=16807*lo-2836*hi;
   
   if (newword < 0)
      newword = newword+2147483647;
   return newword;
endfunction

function Randtable lcong(int seed);
   Randtable v;
   v[0]=seed;
   for(Integer i=1;i<valueof(DEG_3);i=i+1)
      v[i]=getnewword(v[i-1]);
   return v;
endfunction

//used only for initialization
module mkLinearCongruential#(Reg#(Randtable) randtable)(LinearCongruential);
   Reg#(int)word<-mkRegU;
   Reg#(Index) i<-mkReg(1);
   Reg#(Bool) finish<-mkReg(False);
   Reg#(Bool) started<-mkReg(False);
   rule lc(started&&!finish);
      Randtable v=randtable;
      int newword=getnewword(word);
      word<=newword;
      v[0]=newword;
      v=rotate(v);
      randtable<=v;
      if(i==finalIndex)finish<=True;
      i<=i+1;
   endrule
   method Action seed(int inSeed) if(!started);
      Randtable v=randtable;
      v[finalIndex]=inSeed;
      randtable<=v;
      word<=inSeed;
      started<=True;
   endmethod
   
   method Action finished if (finish);
   endmethod
endmodule

endpackage
