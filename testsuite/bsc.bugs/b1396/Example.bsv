package Example;

import TLM::*;
//import TLMDefines::*;

typedef Bit#(16) T;

typeclass BusPayload#(type a);
   function TLMId getId(a payload);
endtypeclass

typeclass TC#(type a);
   function T getId(a payload);
endtypeclass

T x = 0;

endpackage

