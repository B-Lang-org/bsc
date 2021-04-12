import GetPut::*;

interface Chunker#(type bitthing, numeric type n);
  interface Get#(Bit#(TMul#(n,SizeOf#(bitthing)))) get;
  interface Put#(Maybe#(bitthing)) put;
endinterface
