package RPC;

import Connectable::*;

interface IRPC#(type a, type r);
   method r fn(a x);
   interface RWire#(a) argwire;
   interface RWire#(r) reswire;
endinterface

interface VIRPC#(type a, type r);
   method r fn(a x);
   method a geta;
   method Action setr(r x);
endinterface

import "BVI" RPC =
module vMkRPC (VIRPC#(a, r))
   provisos (Bits#(a,sa), Bits#(r,sr));

   parameter widtha = valueOf(sa);   
   parameter widthr = valueOf(sr);
   default_clock clk();
   default_reset rst();

   method RESULT fn (ARG);
   method ARGW geta;
   method setr(RESW) enable (SETR);

   schedule fn CF (geta, setr);
   schedule geta CF (geta, setr);

   path (ARG, ARGW);
   path (SETR, RESULT);
endmodule

module mkRPC(IRPC#(a, r))
   provisos (Bits#(a,sa), Bits#(r,sr));

   VIRPC#(a,r) vrpc <- vMkRPC;

   method fn = vrpc.fn;

   interface RWire argwire;
      method wget = tagged Valid vrpc.geta;
      method wset(x) = noAction;
   endinterface

   interface RWire reswire;
      method wget = tagged Invalid;
      method wset = vrpc.setr;
   endinterface
endmodule

// ====
      
endpackage
