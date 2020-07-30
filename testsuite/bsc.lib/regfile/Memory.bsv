import RegFile::*;

typedef Bit#(5) Address;
typedef Bit#(12) Data;

interface Memory;
   method Data read_mem(Address addr);
   method Action write_mem(Address addr, Data data);
endinterface


module mkMemory(Memory);
   RegFile#(Address, Data) mem <- mkRegFileFullLoadBin("parse-test.bin");

   method read_mem(addr);
      return mem.sub(addr);
   endmethod

   method Action write_mem(addr,data);
      mem.upd(addr,data);
   endmethod

endmodule
