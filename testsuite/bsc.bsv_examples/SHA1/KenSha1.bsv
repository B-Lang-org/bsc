package KenSha1;
import ClientServer::*;
import GetPut::*;
import Vector::*;
import FIFOF::*;
import SpecialFIFOs::*;

import StmtFSM::*;

typedef struct {
   Bit#(32) a;
   Bit#(32) b;
   Bit#(32) c;
   Bit#(32) d;
   Bit#(32) e;
   } ShaState deriving (Bits);
typedef Vector#(16,Bit#(32)) InputChunk;
typedef Vector#(80,Bit#(32)) V80;

ShaState initialH=ShaState 
{a:'h67452301
,b:'hEFCDAB89
,c:'h98BADCFE
,d:'h10325476
,e:'hC3D2E1F0
};

function ShaState stateAdd(ShaState x, ShaState y);
   return ShaState
   { a: x.a+y.a
    ,b: x.b+y.b
    ,c: x.c+y.c
    ,d: x.d+y.d
    ,e: x.e+y.e};
endfunction

function ShaState hAdd(ShaState x);
   return stateAdd(initialH,x);
endfunction


Bit#(32) k0='h5A827999;
Bit#(32) k1='h6ED9EBA1;
Bit#(32) k2='h8F1BBCDC;
Bit#(32) k3='hCA62C1D6;

function Bit#(32) leftrotate(Bit#(32)x, Bit#(n) dummy) provisos (Add#(n,m,32));
   Tuple2#(Bit#(n),Bit#(m)) s=split(x);
   return{tpl_2(s),tpl_1(s)};
endfunction

function Bit#(32) f0(ShaState x);
   return (x.b&x.c)|((~x.b)&x.d);
endfunction

function Bit#(32) parity(ShaState x);
   return x.b^x.c^x.d;
endfunction

function Bit#(32) f1(ShaState x);
   return parity(x);
endfunction

function Bit#(32) f2(ShaState x);
   return (x.b&x.c)|(x.b&x.d)|(x.c&x.d);
endfunction

function Bit#(32) get_f(Integer i,ShaState x);
   if (i<20)
      return f0(x);
   else if (i<40)
      return f1(x);
   else if (i<60)
      return f2(x);
   else 
      return f1(x);
endfunction

function Bit#(32) get_k(Integer i);
   if (i<20)
      return k0;
   else if (i<40)
      return k1;
   else if (i<60)
      return k2;
   else 
      return k3;
endfunction
   
function ShaState round_do(ShaState x, Bit#(32) w, Bit#(32) k, Bit#(32) f);
      return ShaState{e:x.d
         ,d:x.c
         ,c:leftrotate(x.b,30'b0)
         ,b:x.a 
         ,a:leftrotate(x.a,5'b0)+f+x.e+k+w };
endfunction   

function ShaState round(Integer i,ShaState x,Bit#(32) w);
   Bit#(32) k=get_k(i);
   Bit#(32) f=get_f(i,x);
   return round_do(x,w,k,f);
endfunction

function Bit#(32) eighty_extend(Bit#(32)a,Bit#(32)b,Bit#(32)c,Bit#(32)d);
   return leftrotate(a^b^c^d,1'b0);
endfunction

function InputChunk make_new_w(InputChunk w);
   Integer ii=16;   
   Vector#(1,Bit#(32)) new_w;
   new_w[0]=eighty_extend(w[ii-3],w[ii-8],w[ii-14],w[ii-16]);
   return append(tail(w),new_w);
endfunction
   
function V80 create_eighty(InputChunk inw);
   V80 w;
   Integer i;
   for(i=0;i<16;i=i+1)
      w[i]=inw[i];
   for(i=16;i<80;i=i+1)
      w[i]=eighty_extend(w[i-3],w[i-8],w[i-14],w[i-16]);
   return w;
endfunction
function ShaState doChunk(InputChunk inw, ShaState x);
   V80 w;
   Integer i;
   w=create_eighty(inw);
   for(i=0;i<80;i=i+1)
      x=round(i,x,w[i]);
   return x;
endfunction

interface InstantSha;
   method ShaState go(InputChunk inw, ShaState x);
endinterface

module mkShaChunk(InstantSha);
   method ShaState go(InputChunk inw, ShaState x);
      return doChunk(inw,x);
   endmethod
endmodule

function InputChunk example_input;
   InputChunk w=unpack(0);
   w[0]='h61626380;
   w[15]=8*3;
   return w;
endfunction
   
function InputChunk mkInput3(Bit#(32) x1, Bit#(32) x2, Bit#(32) length);
   InputChunk w=unpack(0);
   w[0]=x1;
   w[1]=x2;
   w[15]=8*length;
   return w;
endfunction  

//boundary needed for aggressive conditions not to explode
//(*synthesize*)
module mkChunk(Server#(InputChunk,ShaState));
   Reg#(InputChunk) w<-mkRegU;
   Reg#(UInt#(7)) i<-mkRegU;
   Reg#(Maybe#(ShaState)) x<-mkReg(Invalid);
   FIFOF#(InputChunk) infifo<-mkSizedBypassFIFOF(1);
   FIFOF#(ShaState) outfifo<-mkSizedBypassFIFOF(1);
   rule newinput (x matches Invalid);
      InputChunk i1<-toGet(infifo).get;
      w<=i1;
      x<=tagged Valid initialH;
      i<=0;
   endrule
   module mkRound#(UInt#(7) left, UInt#(7) right, Bit#(32)k, function Bit#(32) f(ShaState x))();
      rule doit (left<=i && i<right &&& x matches tagged Valid .jx);
         InputChunk new_w=make_new_w(w);
         x<=tagged Valid (round_do(jx,last(new_w),k,f(jx)));
         w<=new_w;
         i<=i+1; 
      endrule
   endmodule
   rule r0_16 (i<16 &&& x matches tagged Valid .jx);
      x<=tagged Valid (round_do(jx,w[i],k0,f0(jx)));
      i<=i+1;
   endrule
   mkRound(16,20,k0,f0);
   mkRound(20,40,k1,parity);
   mkRound(40,60,k2,f2);
   mkRound(60,80,k3,parity);
   
   rule r80 (i==80 &&& x matches tagged Valid .jx);
      outfifo.enq(hAdd(jx));
      x<=tagged Invalid;
   endrule
   
   /*
   rule peek (x matches tagged Valid .s);
      $display("peek %d a %h b %h c %h d %h e %h",i,s.a,s.b,s.c,s.d,s.e);
   endrule
    */
   interface Put request=toPut(infifo);
   interface Get response=toGet(outfifo);
      
endmodule   
   

module sysKenSha1();
   Server#(InputChunk,ShaState) r<-mkChunk;
   mkAutoFSM(seq
             r.request.put(mkInput3('h65667a77,'h65746980,7));//efzweti
             action
                ShaState s<-r.response.get;
                $display("final a %h b %h c %h d %h e %h",s.a,s.b,s.c,s.d,s.e);
             endaction
             endseq);
endmodule

module mkTop1();
   Reg#(ShaState) x<-mkReg(initialH);
   Reg#(InputChunk) inw<-mkReg(example_input);
   InstantSha ii<-mkShaChunk;
   Reg#(int) c<-mkReg(0);
   rule fov;
      ShaState s=ii.go(inw,x);
      $display("a %h b %h c %h d %h e %h",s.a,s.b,s.c,s.d,s.e);
   endrule
   rule inccc;
      c<=c+1;
   endrule
   rule endddd(c==10);
      $finish(0);
   endrule
      
endmodule

endpackage
