
import GetPut::*;
import FIFO::*;

// ============

typedef struct {
   addr_t address;
} Req #(type addr_t) deriving(Eq, Bits);

interface Ifc;
   // polymorphic subinterface
   interface Get#(Req#(ctr_addr_t)) request;
endinterface

module sysTest (Get#(Req#(ctr_addr_t)))
   provisos (Bits#(ctr_addr_t, cas));

   module mkSubMod(Ifc);
      FIFO#(Req#(ctr_addr_t)) reqFF <- mkFIFO;
      interface Get request = toGet(reqFF);
   endmodule

   let s <- mkSubMod;
   return s.request;
endmodule

