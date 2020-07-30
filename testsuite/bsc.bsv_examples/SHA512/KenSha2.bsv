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

typedef 64 WidthWord;
typedef Bit#(WidthWord) Word;
typedef UInt#(7) CountRounds;
typedef 80 NumRounds;
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
) | bc | perl -nwe 'print "," unless $.==1;die unless /\.([0-9A-F]{16})/;$h=$1; print "",chr($.+96),": 64\x27h$h\n"'
*/

ShaState initialH=ShaState{
a: 64'h6A09E667F3BCC908
,b: 64'hBB67AE8584CAA73B
,c: 64'h3C6EF372FE94F82B
,d: 64'hA54FF53A5F1D36F1
,e: 64'h510E527FADE682D1
,f: 64'h9B05688C2B3E6C1F
,g: 64'h1F83D9ABFB41BD6B
,h: 64'h5BE0CD19137E2179
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
echo 'forprime(p=2,409,print("cbrt(",p,")"))' | gp -q | grep cbrt
) | bc -l | perl -nwe 'print "," unless $.==1;die unless /\.([0-9A-F]{16})/;$h=$1;print " 64\x27h$h";END{print "\n"}'
*/

Word k_round_constant[valueof(NumRounds)]={
 64'h428A2F98D728AE22, 64'h7137449123EF65CD, 64'hB5C0FBCFEC4D3B2F, 64'hE9B5DBA58189DBBC, 64'h3956C25BF348B538, 64'h59F111F1B605D019, 64'h923F82A4AF194F9B, 64'hAB1C5ED5DA6D8118, 64'hD807AA98A3030242, 64'h12835B0145706FBE, 64'h243185BE4EE4B28C, 64'h550C7DC3D5FFB4E2, 64'h72BE5D74F27B896F, 64'h80DEB1FE3B1696B1, 64'h9BDC06A725C71235, 64'hC19BF174CF692694, 64'hE49B69C19EF14AD2, 64'hEFBE4786384F25E3, 64'h0FC19DC68B8CD5B5, 64'h240CA1CC77AC9C65, 64'h2DE92C6F592B0275, 64'h4A7484AA6EA6E483, 64'h5CB0A9DCBD41FBD4, 64'h76F988DA831153B5, 64'h983E5152EE66DFAB, 64'hA831C66D2DB43210, 64'hB00327C898FB213F, 64'hBF597FC7BEEF0EE4, 64'hC6E00BF33DA88FC2, 64'hD5A79147930AA725, 64'h06CA6351E003826F, 64'h142929670A0E6E70, 64'h27B70A8546D22FFC, 64'h2E1B21385C26C926, 64'h4D2C6DFC5AC42AED, 64'h53380D139D95B3DF, 64'h650A73548BAF63DE, 64'h766A0ABB3C77B2A8, 64'h81C2C92E47EDAEE6, 64'h92722C851482353B, 64'hA2BFE8A14CF10364, 64'hA81A664BBC423001, 64'hC24B8B70D0F89791, 64'hC76C51A30654BE30, 64'hD192E819D6EF5218, 64'hD69906245565A910, 64'hF40E35855771202A, 64'h106AA07032BBD1B8, 64'h19A4C116B8D2D0C8, 64'h1E376C085141AB53, 64'h2748774CDF8EEB99, 64'h34B0BCB5E19B48A8, 64'h391C0CB3C5C95A63, 64'h4ED8AA4AE3418ACB, 64'h5B9CCA4F7763E373, 64'h682E6FF3D6B2B8A3, 64'h748F82EE5DEFB2FC, 64'h78A5636F43172F60, 64'h84C87814A1F0AB72, 64'h8CC702081A6439EC, 64'h90BEFFFA23631E28, 64'hA4506CEBDE82BDE9, 64'hBEF9A3F7B2C67915, 64'hC67178F2E372532B, 64'hCA273ECEEA26619C, 64'hD186B8C721C0C207, 64'hEADA7DD6CDE0EB1E, 64'hF57D4F7FEE6ED178, 64'h06F067AA72176FBA, 64'h0A637DC5A2C898A6, 64'h113F9804BEF90DAE, 64'h1B710B35131C471B, 64'h28DB77F523047D84, 64'h32CAAB7B40C72493, 64'h3C9EBE0A15C9BEBC, 64'h431D67C49C100D4C, 64'h4CC5D4BECB3E42B6, 64'h597F299CFC657E2A, 64'h5FCB6FAB3AD6FAEC, 64'h6C44198C4A475817
};

function Word rightrotate(Word x, Bit#(n) dummy) provisos (Add#(n,m,WidthWord));
   Tuple2#(Bit#(m),Bit#(n)) s=split(x);
   return{tpl_2(s),tpl_1(s)};
endfunction

function Word initial_extend(InputChunk w);
   Integer i=16;
   Word fifteen = w[i-15];
   Word s0 = rightrotate(fifteen,1'b0)
   ^ rightrotate(fifteen,8'b0)
   ^ (fifteen>>7);
   Word two = w[i-2];
   Word s1 =rightrotate(two,19'b0)
   ^ rightrotate(two,61'b0)
   ^ (two>>6);
   return w[i-16]+s0+w[i-7]+s1;
endfunction

function ShaState round_do(ShaState x, Word k, Word w);
   Word s1 = rightrotate(x.e,14'b0)
   ^ rightrotate(x.e,18'b0)
   ^ rightrotate(x.e,41'b0);
   Word ch = (x.e & x.f) ^ (~x.e & x.g);
   Word temp = x.h + s1 + ch + k + w;
   x.d = x.d + temp;
   Word s0 = rightrotate(x.a, 28'b0)
   ^ rightrotate(x.a, 34'b0)
   ^ rightrotate(x.a, 39'b0);
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

// two block test vector from
// http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA512.pdf
// abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu
typedef TSub#(SizeInput,BitCounter) ExampleLength;
typedef Bit#(ExampleLength) Example_bits;
Word long_array[16]={
64'h6162636465666768, 64'h6263646566676869, 64'h636465666768696a, 64'h6465666768696a6b, 64'h65666768696a6b6c, 64'h666768696a6b6c6d, 64'h6768696a6b6c6d6e, 64'h68696a6b6c6d6e6f, 64'h696a6b6c6d6e6f70, 64'h6a6b6c6d6e6f7071, 64'h6b6c6d6e6f707172, 64'h6c6d6e6f70717273, 64'h6d6e6f7071727374, 64'h6e6f707172737475, {1'b1,0}, 0};
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

typedef 102400 DataMax;
// cat ../../bplay/shab*testvectors/SHA512*Msg.rsp | perl longmsgparse.pl > input.hex
module regfile();
   Integer numtests=2306;
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
