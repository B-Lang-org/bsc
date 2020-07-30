
// AES variables
typedef Bit#(8)  UBYTE;
typedef Bit#(32) UWORD;


typedef union tagged
{
  void      Nop;          // tag[2:0]=0, data=....
  UWORD     Encrypt128;   // tag[3:0]=1, data=data[31:0]
  UWORD     Encrypt192;   // tag[3:0]=2, data=data[31:0]
  UWORD     Encrypt256;   // tag[3:0]=3, data=data[31:0]
  UWORD     Decrypt128;   // tag[3:0]=4, data=data[31:0]
  UWORD     Decrypt192;   // tag[3:0]=5, data=data[31:0]
  UWORD     Decrypt256;   // tag[3:0]=6, data=data[31:0]
  UWORD     AesReturn;    // tag[3:0]=7, data=data[31:0]

  UWORD     DesIn;        // etc, etc, etc
  UWORD     DesReturn;

  UWORD     EccIn;
  UWORD     EccReturn;

  UWORD     RsaIn;
  UWORD     RsaReturn;

} TBus      deriving (Bits, Eq);

UWORD addrAES = 'h100;
UWORD addrDES = 'h200;
UWORD addrRSA = 'h300;
UWORD addrECC = 'h400;

interface DBus;
   method Action             push(TBus d);
   method ActionValue#(TBus) pop();
endinterface

import Vector::*;

typedef UWORD   TData;
typedef Bit#(128) W128;
typedef Vector#(16,UBYTE) VBytes;

/*
function VBytes convertWordsToBytes( W128 d );
   VBytes res = ?;
   for (Integer i=0; i<15; i=i+1) begin
      res[i] = truncate(d);
      d = d >> 8;
   end
   return res;
endfunction
*/

function Bit#(n) fromReg ( Reg#(Bit#(n)) x );
   return x._read();
endfunction

   
