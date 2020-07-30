// interfaces to microprocessor and the memory being cached

import SRAM_Interfaces::*;

typedef Bit #(32) Addr;
typedef Bit #(256) Line;

interface IFC_Cache_Processor;
    method Action p2c(SRAM_Request_t#(Addr, Line) cpu_request);
    method SRAM_Response_t#(Line) c2p;
endinterface: IFC_Cache_Processor

interface IFC_Cache_Memory;
    method SRAM_Request_t#(Addr, Line) c2m();
    method Action m2c_ack();
    method Action m2c(SRAM_Response_t#(Line) abc);
endinterface: IFC_Cache_Memory

interface IFC_Cache;
    interface IFC_Cache_Processor proc;
    interface IFC_Cache_Memory mem;
endinterface: IFC_Cache

