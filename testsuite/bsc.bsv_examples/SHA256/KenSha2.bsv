package KenSha2;

/*
 A implementation of the SHA-256 cryptographic hash algorithm (part
 of the SHA-2 family of hash functions), one cycle per iteration.

 There are three interfaces.  The highest-level interface, "bitSHA2",
 consumes bits terminated by EOF and returns a hash.  "mkBlockProcess"
 consumes blocks and returns a hash.  The user is expected to have
 properly padded the input.  "mkSHA2" is "reentrant", consuming
 blocks.  The user must thread the state between successive calls.

 Although there is bitSHA2, there is no byteSHA2 that consumes bytes,
 though it could probably be easily written.

 There are probably FIFOs that could by optimized with bypasses.
*/

import Vector::*;
import ClientServer::*;
import GetPut::*;
import FIFO::*;
import Connectable::*;
import RegFile::*;
/*
 Probably eventually want
import FIFOF::*;
import SpecialFIFOs::*;
*/

import StmtFSM::*;

typedef 32 WidthWord;
typedef Bit#(WidthWord) Word;
typedef UInt#(7) CountRounds;
typedef 64 NumRounds;
typedef struct {
   Word a;
   Word b;
   Word c;
   Word d;
   Word e;
   Word f;
   Word g;
   Word h;
   } ShaState deriving (Bits);

function ShaState stateAdd(ShaState x, ShaState y);
   return ShaState
   { a: x.a+y.a
    ,b: x.b+y.b
    ,c: x.c+y.c
    ,d: x.d+y.d
    ,e: x.e+y.e
    ,f: x.f+y.f
    ,g: x.g+y.g
    ,h: x.h+y.h
    };
endfunction

//This is 16*32 = 512 or 16*64 = 1024 depending
//on WidthWord, but always 16 words
typedef 16 InputWords;
typedef Vector#(InputWords,Word) InputChunk;
typedef TMul#(InputWords,WidthWord) SizeInput;
typedef UInt#(TAdd#(TLog#(SizeInput),1)) CountBlock;

/*
#! /bin/bash
set -x
set -o pipefail
set -e
(
cat <<EOF
scale=30
obase=16
EOF
echo 'forprime(p=2,19,print("sqrt(",p,")"))' | gp -q | grep sqrt
) | bc | perl -nwe 'print "," unless $.==1;die unless /\.([0-9A-F]{8})/;$h=$1; print "",chr($.+96),": 32\x27h$h\n"'
*/

ShaState initialH=ShaState{
a: 32'h6A09E667
,b: 32'hBB67AE85
,c: 32'h3C6EF372
,d: 32'hA54FF53A
,e: 32'h510E527F
,f: 32'h9B05688C
,g: 32'h1F83D9AB
,h: 32'h5BE0CD19
};

/*
#! /bin/bash
set -x
set -o pipefail
set -e
(
cat <<EOF
define cbrt(x) {
return e(l(x)/3)
}
scale=30
obase=16
EOF
echo 'forprime(p=2,311,print("cbrt(",p,")"))' | gp -q | grep cbrt
) | bc -l | perl -nwe 'print "," unless $.==1;die unless /\.([0-9A-F]{8})/;$h=$1;print " 32\x27h$h";END{print "\n"}'
*/

Word k_round_constant[valueof(NumRounds)]={
 32'h428A2F98, 32'h71374491, 32'hB5C0FBCF, 32'hE9B5DBA5, 32'h3956C25B, 32'h59F111F1, 32'h923F82A4, 32'hAB1C5ED5, 32'hD807AA98, 32'h12835B01, 32'h243185BE, 32'h550C7DC3, 32'h72BE5D74, 32'h80DEB1FE, 32'h9BDC06A7, 32'hC19BF174, 32'hE49B69C1, 32'hEFBE4786, 32'h0FC19DC6, 32'h240CA1CC, 32'h2DE92C6F, 32'h4A7484AA, 32'h5CB0A9DC, 32'h76F988DA, 32'h983E5152, 32'hA831C66D, 32'hB00327C8, 32'hBF597FC7, 32'hC6E00BF3, 32'hD5A79147, 32'h06CA6351, 32'h14292967, 32'h27B70A85, 32'h2E1B2138, 32'h4D2C6DFC, 32'h53380D13, 32'h650A7354, 32'h766A0ABB, 32'h81C2C92E, 32'h92722C85, 32'hA2BFE8A1, 32'hA81A664B, 32'hC24B8B70, 32'hC76C51A3, 32'hD192E819, 32'hD6990624, 32'hF40E3585, 32'h106AA070, 32'h19A4C116, 32'h1E376C08, 32'h2748774C, 32'h34B0BCB5, 32'h391C0CB3, 32'h4ED8AA4A, 32'h5B9CCA4F, 32'h682E6FF3, 32'h748F82EE, 32'h78A5636F, 32'h84C87814, 32'h8CC70208, 32'h90BEFFFA, 32'hA4506CEB, 32'hBEF9A3F7, 32'hC67178F2
};

function Word rightrotate(Word x, Bit#(n) dummy) provisos (Add#(n,m,WidthWord));
   Tuple2#(Bit#(m),Bit#(n)) s=split(x);
   return{tpl_2(s),tpl_1(s)};
endfunction

function Word initial_extend(InputChunk w);
   Integer i=16;
   Word fifteen = w[i-15];
   Word s0 = rightrotate(fifteen,7'b0)
   ^ rightrotate(fifteen,18'b0)
   ^ (fifteen>>3);
   Word two = w[i-2];
   Word s1 =rightrotate(two,17'b0)
   ^ rightrotate(two,19'b0)
   ^ (two>>10);
   return w[i-16]+s0+w[i-7]+s1;
endfunction

function ShaState round_do(ShaState x, Word k, Word w);
   Word s1 = rightrotate(x.e,6'b0)
   ^ rightrotate(x.e,11'b0)
   ^ rightrotate(x.e,25'b0);
   Word ch = (x.e & x.f) ^ (~x.e & x.g);
   Word temp = x.h + s1 + ch + k + w;
   x.d = x.d + temp;
   Word s0 = rightrotate(x.a, 2'b0)
   ^ rightrotate(x.a, 13'b0)
   ^ rightrotate(x.a, 22'b0);
   Word maj = (x.a & (x.b ^ x.c)) ^ (x.b & x.c);
   temp = temp + s0 + maj;
   return ShaState
   { h: x.g
    ,g: x.f
    ,f: x.e
    ,e: x.d
    ,d: x.c
    ,c: x.b
    ,b: x.a
    ,a: temp
    };
endfunction

function InputChunk mkInput3(Word x1, Word x2, Word length);
   InputChunk w=unpack(0);
   w[0]=x1;
   w[1]=x2;
   w[15]=8*length;
   return w;
endfunction

module mkInputExtend(Server#(InputChunk,Word));
   Reg#(InputChunk) w<-mkRegU;
   interface Put request;
      method Action put(InputChunk inw);
         w<=inw;
      endmethod
   endinterface
   interface Get response;
      method ActionValue#(Word) get;
         Word ret=w[0];
         InputChunk neww=rotate(w);
         neww[15]=initial_extend(w);
         w<=neww;
         return ret;
      endmethod
   endinterface
endmodule

module mkSHA2(Server#(Tuple2#(ShaState,InputChunk),ShaState));
   Reg#(Maybe#(ShaState)) x<-mkReg(tagged Invalid);
   Reg#(CountRounds) i<-mkReg(0);
   FIFO#(Tuple2#(ShaState,InputChunk)) infifo <- mkFIFO;
   FIFO#(ShaState) outfifo <- mkFIFO;
   Server#(InputChunk,Word) input_w<-mkInputExtend;
   CountRounds cNumRounds=fromInteger(valueof(NumRounds));

   //Use this vector instead of a giant lookup table, which would have
   //presumably implemented by a giant variable shifter.
   Reg#(Vector#(NumRounds,Word)) k <- mkReg(arrayToVector(k_round_constant));

   rule initialize (x matches tagged Invalid);
      x <= tagged Valid (tpl_1(infifo.first));
      input_w.request.put(tpl_2(infifo.first));
      //Do not dequeue until "done" so "first" is available then
      //to add the last x.
      i <= 0;
   endrule

   rule oneround ( i<cNumRounds &&& x matches tagged Valid .jx );
      Word w<-input_w.response.get;
      x<=tagged Valid round_do(jx,k[0],w);
      k<=rotate(k);  // rely that it rotates completely around for each block
      i<=i+1;
   endrule
   rule done(i==cNumRounds &&& x matches tagged Valid .jx);
      infifo.deq;
      outfifo.enq(stateAdd(tpl_1(infifo.first),jx));
      x <= tagged Invalid;
   endrule

   interface Put request=toPut(infifo);
   interface Get response=toGet(outfifo);
endmodule

typedef union tagged {
   void EOF;
   a ValidData;
   } DataOrEof#(type a) deriving(Bits,FShow);

module mkBlockProcess(Server#(DataOrEof#(InputChunk),ShaState));
   Reg#(Maybe#(ShaState)) s<-mkReg(tagged Valid initialH);
   Server#(Tuple2#(ShaState,InputChunk),ShaState) r<-mkSHA2;
   FIFO#(ShaState) outfifo<-mkFIFO;
   rule process (s matches tagged Invalid);
      //the rule condition might be redundant
      ShaState new_s<-r.response.get;
      s<= tagged Valid new_s;
   endrule
   interface Put request;
      method Action put(DataOrEof#(InputChunk) mi) if (s matches tagged Valid .js);
         //$display(fshow(mi));
         case (mi) matches
            tagged ValidData .i : action
               r.request.put(tuple2(js,i));
               s<= tagged Invalid;
            endaction
            tagged EOF : action
               outfifo.enq(js);
               s<= tagged Valid initialH;
            endaction
         endcase

      endmethod
   endinterface
   interface Get response = toGet(outfifo);
endmodule

function Action shaprint(ShaState s);
   $display("%h%h%h%h%h%h%h%h",
      //$display("%h %h %h %h %h %h %h %h",
            s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h);
endfunction

function Action getprint(Get#(ShaState) g);
   action
      ShaState out <- g.get;
      shaprint(out);
   endaction
endfunction

//This happens to be true according to the sha256 and sha512 specifications
//but it does not necessarily have to be.
typedef TAdd#(WidthWord,WidthWord) BitCounter;

interface CounterD;
   method Action inc;
   method ActionValue#(Bit#(BitCounter)) read_and_reset;
endinterface

module mkDataCounter(CounterD);
   Reg#(UInt#(BitCounter)) dataSize<-mkReg(0);
   method Action inc;
      dataSize<=dataSize+1;
   endmethod
   method ActionValue#(Bit#(BitCounter)) read_and_reset;
      dataSize<=0;
      return pack(dataSize);
   endmethod
endmodule

//potential utility
interface SingleMethod#(type t_in, type t_out);
   method t_out go(t_in x);
endinterface

typedef enum {Normal,Padding,LastBlock} PadState deriving (Bits,Eq);
module bitLoader(Server#(DataOrEof#(bit),DataOrEof#(InputChunk)));
   FIFO#(DataOrEof#(bit)) infifo<-mkFIFO;
   FIFO#(DataOrEof#(InputChunk)) outfifo<-mkFIFO;
   CountBlock blockWithoutLength=fromInteger(valueof(TSub#(SizeInput,BitCounter)));
   Reg#(CountBlock) blockSize<-mkReg(0);
   CounterD dataSize<-mkDataCounter;
   Reg#(Bit#(SizeInput)) current<-mkRegU;
   CountBlock fullSize=fromInteger(valueof(SizeInput));
   //FIFO#(bit) internal <- mkFIFO;
   Reg#(PadState) padState<-mkReg(Normal);
   module guardcurrent(SingleMethod#(bit,Action));
      // The purpose of this submodule is to automatically propagate the method condition.
      // Otherwise, we would have just used a function.
      method Action go(bit b) if (blockSize<fullSize);
         current<={truncate(current),b};
         blockSize<=blockSize+1;
      endmethod
   endmodule
   SingleMethod#(bit,Action) addBit <- guardcurrent;
   rule dovalid (padState==Normal && blockSize<fullSize &&& infifo.first matches tagged ValidData .b);
      dataSize.inc;
      addBit.go(b);
      infifo.deq;
   endrule
   rule blockfull (blockSize == fullSize);
      // data in nybbles comes in 0 1 2 3 4 5 6 7 8 A B C
      // goal is {01234567,8ABC0000}
      // normal unpack would require 'h8abc000001234567
      // which is unreasonable
      outfifo.enq(tagged ValidData (unpackBits(current)));
      blockSize<=0;
   endrule
   rule doEof (padState==Normal &&& infifo.first matches tagged EOF);
      addBit.go(1);
      padState<=Padding;
      infifo.deq;
   endrule
   rule doPadding(padState==Padding
      && blockSize!=blockWithoutLength);
      addBit.go(0);
   endrule
   rule doSize(padState==Padding
      && blockSize==blockWithoutLength);
      Bit#(BitCounter) bd <- dataSize.read_and_reset;
      current<={truncate(current),bd};
      blockSize<=fullSize;
      padState<=LastBlock;
   endrule
   rule doLastBlock(padState==LastBlock && blockSize==0);
      outfifo.enq(tagged EOF);
      padState<=Normal;
   endrule
   interface Put request = toPut(infifo);
   interface Get response=toGet(outfifo);
endmodule

function InputChunk unpackBits(Bit#(SizeInput) b);
   // bits are 01234567890
   // and we want {0123,4567,8900}
   InputChunk ic;
   for(Integer i=0;i<valueof(InputWords);i=i+1) begin
      ic[i]=tpl_1(split(b));
      b= b << valueof(WidthWord);
   end
   return ic;
endfunction

// two block test vector from http://csrc.nist.gov/groups/STM/cavp/documents/shs/sha256-384-512.pdf
// abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq
typedef TSub#(SizeInput,BitCounter) ExampleLength;
typedef Bit#(ExampleLength) Example_bits;
Word long_array[16]={32'h61626364, 32'h62636465, 32'h63646566, 32'h64656667, 32'h65666768, 32'h66676869, 32'h6768696a, 32'h68696a6b, 32'h696a6b6c, 32'h6a6b6c6d, 32'h6b6c6d6e, 32'h6c6d6e6f, 32'h6d6e6f70, 32'h6e6f7071, {1'b1,0}, 0};
Vector#(16,Word) long_vector=arrayToVector(long_array);
Example_bits long_bits = concat14(long_vector);
//Curiously, array initialization and bit concatenation have the same syntax.

function Example_bits concat14(Vector#(16,Word) x);
   Example_bits out=0;
   for(Integer i=0;i<14;i=i+1)
      out = (out << valueof(WidthWord)) | zeroExtend(x[i]);
   return out;
endfunction

module twoChunk();
   InputChunk first=long_vector;
   InputChunk second= unpack(0);
   second[15]=fromInteger(valueof(ExampleLength));
   Server#(DataOrEof#(InputChunk),ShaState) block_processor <- mkBlockProcess;
   InputChunk zero=unpack(0);
   zero[0]={1'b1,0};
   Empty load <- mkAutoStartFSM
   (seq
       block_processor.request.put(tagged ValidData first);
       block_processor.request.put(tagged ValidData second);
       block_processor.request.put(tagged EOF);
       block_processor.request.put(tagged ValidData zero);
       block_processor.request.put(tagged EOF);
       block_processor.request.put(tagged ValidData zero);
       block_processor.request.put(tagged EOF);
       block_processor.request.put(tagged ValidData first);
       block_processor.request.put(tagged ValidData second);
       block_processor.request.put(tagged EOF);
    endseq);
   mkAutoFSM
   (seq
    getprint(block_processor.response);
    getprint(block_processor.response);
    getprint(block_processor.response);
    getprint(block_processor.response);
    endseq);
endmodule

// Same as mkAutoFSM but does not call finish.
// potential utility
module mkAutoStartFSM#(Stmt stmts)();
   Reg#(Bool) running <- mkReg(False);
   FSM test_fsm <- mkFSM(stmts);
   rule auto_start (!running);
      test_fsm.start;
      running<=True;
   endrule
endmodule


module oneChunk();
   Server#(Tuple2#(ShaState,InputChunk),ShaState) r<-mkSHA2;
   //InputChunk i=mkInput3(32'h65667a77,32'h65746980,7);//efzweti

   InputChunk i0=long_vector;
   InputChunk second= unpack(0);
   second[15]=fromInteger(valueof(ExampleLength));
   Reg#(ShaState) s<-mkReg(initialH);
   mkAutoFSM(seq
      r.request.put(tuple2(s,i0));
      action
      ShaState temp<-r.response.get;
      s<=temp;
      endaction
         $display("first a %h b %h c %h d %h e %h f %h g %h h %h",
                  s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h);
      r.request.put(tuple2(s,second));
      action
      ShaState temp<-r.response.get;
      s<=temp;
      endaction
         $display("final a %h b %h c %h d %h e %h f %h g %h h %h",
                  s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h);
      endseq);
endmodule

module test();
   Bit#(SizeInput) b='b1101001000;
   InputChunk ic=unpackBits(b);
   //ic[0]=32'h8000_0000;
   mkAutoFSM(seq
      $display(fshow(ic));
      endseq
      );
endmodule

//potential utility
function bit high_bit(Bit#(n) x)
   provisos (Add#(1,_,n));
   return tpl_1(split(x));
endfunction
//potential utility
function Integer datasizeof(a x)
   provisos (Bits#(a,n));
   return valueof(n);
endfunction
module bittest();
   Server#(DataOrEof#(bit),DataOrEof#(InputChunk)) b<-bitLoader;
   Server#(DataOrEof#(InputChunk),ShaState) block_processor <- mkBlockProcess;
   Empty c<-mkConnection(b.response,block_processor.request);
   Reg#(UInt#(BitCounter)) i<-mkRegU;
   Reg#(Example_bits) longt<- mkReg(long_bits);
   Stmt do_long =
    seq
       for(i<=0;i<fromInteger(datasizeof(longt));i<=i+1)
          action
             b.request.put(tagged ValidData high_bit(longt));
             longt <= longt << 1;
          endaction
       action
          b.request.put(tagged EOF);
          longt<=long_bits; //reset it
       endaction
    endseq;
   Reg#(Bit#(24)) text<-mkReg(24'h616263); //abc
   Stmt do_short =
   seq
      for(i<=0;i<fromInteger(datasizeof(text));i<=i+1)
         action
            b.request.put(tagged ValidData high_bit(text));
            text <= text << 1;
         endaction
      action
         b.request.put(tagged EOF);
         text <= 24'h616263; //reset it
      endaction
   endseq;

   mkAutoStartFSM
   (seq
       do_long;
       do_short;
       //empty string
       b.request.put(tagged EOF);
    endseq);
   mkAutoFSM
   (seq
       getprint(block_processor.response);
       getprint(block_processor.response);
       getprint(block_processor.response);
    endseq);

endmodule

module bitSHA2(Server#(DataOrEof#(bit),ShaState));
   Server#(DataOrEof#(bit),DataOrEof#(InputChunk)) b<-bitLoader;
   Server#(DataOrEof#(InputChunk),ShaState) block_processor <- mkBlockProcess;
   Empty c<-mkConnection(b.response,block_processor.request);
   interface Put request = b.request;
   interface Get response = block_processor.response;
endmodule

typedef 51200 DataMax;
// cat shab*testvectors/SHA256*Msg.rsp | perl longmsgparse.pl >| input.hex
module regfile();
   Integer numtests=1154;
   Server#(DataOrEof#(bit),ShaState) sha <- bitSHA2;
   RegFile#(UInt#(48),Bit#(DataMax)) data_in<-mkRegFileLoad("input.hex",0,fromInteger(2*numtests-1));
   Reg#(Bit#(DataMax)) text<-mkRegU;
   Reg#(UInt#(BitCounter)) i<-mkRegU;
   Reg#(UInt#(48)) test<-mkRegU;
   //UInt#(BitCounter) len = unpack(truncate(data_in.sub(2*test)));
   Reg#(UInt#(BitCounter)) len <- mkRegU;
   mkAutoStartFSM
   (seq
    for(test<=0;test<fromInteger(numtests);test<=test+1)
       seq
          action
             len<= unpack(truncate(data_in.sub(2*test)));
             text<=data_in.sub(2*test+1);
             endaction
          //$display("length ",len);
          //$display("%x",text);
          for(i<=0;i<len;i<=i+1)
             action
                sha.request.put(tagged ValidData high_bit(text));
                text <= text << 1;
             endaction
          sha.request.put(tagged EOF);
       endseq
    endseq);
   mkAutoFSM
   (seq
       repeat (fromInteger(numtests))
       seq
          delay(1); //needed to avoid a bug
          getprint(sha.response);
       endseq
    endseq);
endmodule

module bug();
   Server#(DataOrEof#(bit),ShaState) sha <- bitSHA2;

   mkAutoStartFSM
   (seq
    sha.request.put(tagged EOF);
    sha.request.put(tagged EOF);
    sha.request.put(tagged EOF);
    endseq);
   mkAutoFSM
   (seq
       repeat (3)
       seq
    //delay 0 has a bug: only two lines output
    //delay 1 works correctly: three lines output
    //Appears to be bug 1790.
          delay(0);
          getprint(sha.response);
       endseq
       $display("done");
    endseq);
endmodule

module sysKenSha2();
   bittest; // SED_TAG for tinderbox
endmodule

endpackage
