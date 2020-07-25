////////////////////////////////////////////////////////////////////////////////
//  Author        : Todd Snyder
//  Description   : Creates Block RAMS for use in FPGAs
////////////////////////////////////////////////////////////////////////////////

// Notes :

package BRAMCore ;

// Export the interfaces
export BRAM_PORT(..);
export BRAM_DUAL_PORT(..);

export BRAM_PORT_BE(..);
export BRAM_DUAL_PORT_BE(..);

// Export the public modules  1 port version
export mkBRAMCore1, mkBRAMCore1Load;
export mkBRAMCore1BE, mkBRAMCore1BELoad;

// Export 2 port version
export mkBRAMCore2, mkBRAMCore2Load;
export mkSyncBRAMCore2, mkSyncBRAMCore2Load;
export mkBRAMCore2BE, mkBRAMCore2BELoad;
export mkSyncBRAMCore2BE, mkSyncBRAMCore2BELoad;

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import Vector :: * ;

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
/// Interfaces
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
/// Single Write Enable Interfaces
////////////////////////////////////////////////////////////////////////////////
(* always_ready *)
interface BRAM_PORT#(type addr, type data);
   method Action put(Bool write, addr address, data datain);
   method data   read();
endinterface: BRAM_PORT

interface BRAM_DUAL_PORT#(type addr, type data);
   interface BRAM_PORT#(addr, data) a;
   interface BRAM_PORT#(addr, data) b;
endinterface

////////////////////////////////////////////////////////////////////////////////
/// Byte Write Enable Interfaces
////////////////////////////////////////////////////////////////////////////////
(* always_ready *)
interface BRAM_PORT_BE#(type addr, type data, numeric type n);
   method Action put(Bit#(n) writeen, addr address, data datain);
   method data   read();
endinterface: BRAM_PORT_BE

interface BRAM_DUAL_PORT_BE#(type addr, type data, numeric type n);
   interface BRAM_PORT_BE#(addr, data, n) a;
   interface BRAM_PORT_BE#(addr, data, n) b;
endinterface


// A model for a null BRAMPort, useful when the data size is 0.    Nothing is instantiated.
// This module is not exported
module vNullBRAMPort (BRAM_PORT#(addr, data));
   return
   (interface  BRAM_PORT
       method Action put(write, address, datain);
          noAction;
       endmethod
       method data   read();
          return ?;
       endmethod
   endinterface);
endmodule

// A model for a null BRAMPort, useful when the data size is 0.    Nothing is instantiated.
// This module is not exported
module vNullBRAMPortBE (BRAM_PORT_BE#(addr, data, n));
   return
   (interface  BRAM_PORT_BE
       method Action put(be, address, datain);
          noAction;
       endmethod
       method data   read();
          return ?;
       endmethod
   endinterface);
endmodule

// A model for a null BRAMPortBE, useful when the addr size is 0.    Nothing is instantiated.
// This module is not exported
module vNullBRAMPort_1word (BRAM_PORT#(addr, data) ifc)
   provisos ( Bits#(data,datasz) );

   Reg#(data) ramdata <- mkRegU ;

   method Action put(write, address, datain);
      if (write) ramdata <= datain ;
   endmethod
   method data   read();
      return ramdata;
   endmethod
endmodule

// A model for a null BRAMPortBE, useful when the addr size is 0.    Nothing is instantiated.
// This module is not exported
module vNullBRAMPortBE_1word (BRAM_PORT_BE#(addr, data, n))
   provisos (
             Bits#(data,data_sz),
             Div#(data_sz, n, chunk_sz),
             Mul#(chunk_sz, n, data_sz)
            );

   Reg#(data) ramdata <- mkRegU ;

   method Action put(be, address, datain);
      if (be != 0 ) begin
         Vector#(n,Vector#(chunk_sz,Bit#(1))) mask = map (replicate, unpack(be));
         Bit#(data_sz) maskb = pack (mask);
         Bit#(data_sz) newdata = (~maskb & pack(ramdata)) | (maskb & pack(datain));

         ramdata <= unpack(newdata);
      end
   endmethod
   method data   read();
      return ramdata ;
   endmethod

endmodule



//////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Single Ported BRAM Definition
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM1 =
module vBRAM1#(
               Integer memSize,
               Bool hasOutputRegister
              ) (BRAM_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO  read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (read);
   schedule put C put;
endmodule: vBRAM1

// Another wrapper layer to support 0 widths
module mkBRAMCore1#(
                    Integer memSize,
                    Bool hasOutputRegister
                   ) (BRAM_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );
   BRAM_PORT#(addr, data) _i = ? ;
   if ( valueOf(data_sz) == 0 )
      (*hide*)
      _i <- vNullBRAMPort ;
   else if (valueOf(addr_sz) == 0 )
      (*hide*)
      _i <- vNullBRAMPort_1word ;
   else
      (*hide*)
      _i <- vBRAM1 (memSize, hasOutputRegister) ;
   return _i;
endmodule

import "BVI" BRAM1Load =
module vBRAM1Load#(
                   Integer memSize,
                   Bool hasOutputRegister,
                   String file, Bool binary
                  ) (BRAM_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter FILENAME   = file;
   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));
   parameter BINARY     = Bit#(1) ' (pack(binary));

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (read);
   schedule put C put;
endmodule: vBRAM1Load


module mkBRAMCore1Load#(
                        Integer memSize,
                        Bool hasOutputRegister,
                        String file, Bool binary
                       ) (BRAM_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   BRAM_PORT#(addr, data) _i = ? ;
   if ( valueOf(data_sz) == 0 || memSize == 0 )
      (*hide*)
      _i <- vNullBRAMPort ;
   else if ( valueOf(addr_sz) == 0 ) begin
      // For address size = 0, there is 1 word of data that must be managed
      // create a module with addr width == 1 to allow safe Verilog simulation
      // and return a shell interface
      (*hide*)
      BRAM_PORT#(Bit#(1), data) _x <- vBRAM1Load (memSize, hasOutputRegister, file, binary) ;
      _i = (interface BRAM_PORT;
               method Action put(Bool writeen, addr address, data datain);
                  _x.put( writeen, 0, datain);
               endmethod
               method data   read() = _x.read ;
            endinterface);
   end
   else
      (*hide*)
      _i <- vBRAM1Load (memSize, hasOutputRegister, file, binary) ;
   return _i;
endmodule

////////////////////////////////////////////////////////////////////////////////
/// Single Ported BRAM Byte Enabled Definition
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM1BE =
module vBRAM1BE#(
                 Integer memSize,
                 Bool hasOutputRegister
                ) (BRAM_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   // This is currently a Bluesim limitation (can support 9-bit byte enables)
   if (valueof(chunk_sz) != 8)           error("Byte enables must control an 8-bit quantity.  You should adjust the width of your data, or the number of write enables.");
   // This is currently an XST limitation
   if (valueof(n) < 1 || valueof(n) > 4) warningM("XST will not infer a BRAM with fewer than 1 write enable or more than 4 write enables.");

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter CHUNKSIZE  = valueof(chunk_sz);
   parameter WE_WIDTH   = valueof(n);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO  read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (read);
   schedule put C put;
endmodule: vBRAM1BE

module mkBRAMCore1BE#(
                      Integer memSize,
                      Bool hasOutputRegister
                     ) (BRAM_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );
   BRAM_PORT_BE#(addr, data, n) _i = ?;
   if ( valueOf(data_sz) == 0 )
      (*hide*)
      _i <- vNullBRAMPortBE ;
   else if (valueOf(addr_sz) == 0 )
      (*hide*)
      _i <- vNullBRAMPortBE_1word ;
   else
      (*hide*)
      _i <- vBRAM1BE (memSize, hasOutputRegister) ;
   return _i;

endmodule

import "BVI" BRAM1BELoad =
module vBRAM1BELoad#(
                     Integer memSize,
                     Bool hasOutputRegister,
                     String file, Bool binary
                    ) (BRAM_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
            );
   // This is currently a Bluesim limitation (can support 9-bit byte enables)
   if (valueof(chunk_sz) != 8)           error("Byte enables must control an 8-bit quantity.  You should adjust the width of your data, or the number of write enables.");
   // This is currently an XST limitation
   if (valueof(n) < 1 || valueof(n) > 4) warningM("XST will not infer a BRAM with fewer than 1 write enable or more than 4 write enables.");

   default_clock   clk(CLK, (*unused*)CLK_GATE);
   default_reset   rst();

   parameter FILENAME   = file;
   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter CHUNKSIZE  = valueof(chunk_sz);
   parameter WE_WIDTH   = valueof(n);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));
   parameter BINARY     = Bit#(1) ' (pack(binary));

   method put(WE, (* reg *)ADDR, (* reg *)DI) enable(EN) clocked_by(clk) reset_by(rst);
   method DO read() clocked_by(clk) reset_by(rst);

   schedule (put, read) CF (read);
   schedule put C put;
endmodule: vBRAM1BELoad

module mkBRAMCore1BELoad#(
                          Integer memSize,
                          Bool hasOutputRegister,
                          String file, Bool binary
                         ) (BRAM_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );
   BRAM_PORT_BE#(addr, data, n) _i = ?;
   if ( valueOf(data_sz) == 0 )
      (*hide*)
      _i <- vNullBRAMPortBE ;
   else if ( valueOf(addr_sz) == 0 ) begin
      // For address size = 0, there is 1 word of data that must be managed
      // create a module with addr width == 1 to allow safe Verilog simulation
      // and return a shell interface
      (*hide*)
      BRAM_PORT_BE#(Bit#(1), data, n) _x <- vBRAM1BELoad (memSize, hasOutputRegister, file, binary) ;
      _i = (interface BRAM_PORT_BE;
               method Action put(Bit#(n) writeen, addr address, data datain);
                  _x.put( writeen, 0, datain);
               endmethod
               method data   read() = _x.read ;
            endinterface);
   end
   else
      (*hide*)
      _i <- vBRAM1BELoad (memSize, hasOutputRegister, file, binary) ;
   return _i;

endmodule





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///
/// Dual Ported BRAM Definition
///
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM2 =
module vSyncBRAM2#(
                   Integer memSize,
                   Bool hasOutputRegister,
                   Clock clkA, Reset rstNA, Clock clkB, Reset rstNB
                  ) (BRAM_DUAL_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   default_clock   no_clock;
   default_reset   no_reset;

   input_clock     clkA(CLKA, (*unused*)CLKA_GATE) = clkA;
   input_clock     clkB(CLKB, (*unused*)CLKB_GATE) = clkB;

   input_reset     rstA() = rstNA;
   input_reset     rstB() = rstNB;

   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));

   interface BRAM_PORT a;
      method put(WEA, (* reg *)ADDRA, (* reg *)DIA) enable(ENA) clocked_by(clkA) reset_by(rstA);
      method DOA read() clocked_by(clkA) reset_by(rstA);
   endinterface: a

   interface BRAM_PORT b;
      method put(WEB, (* reg *)ADDRB, (* reg *)DIB) enable(ENB) clocked_by(clkB) reset_by(rstB);
      method DOB read() clocked_by(clkB) reset_by(rstB);
   endinterface: b
   schedule (a_read) CF (a_put, a_read);
   schedule a_put C a_put;
   schedule (b_read) CF (b_put, b_read);
   schedule b_put C b_put;
endmodule: vSyncBRAM2

module vNullBRAM2#(
                   Integer memSize, Bool hasOutputRegister,
                   Clock clka, Reset reseta,
                   Clock clkb, Reset resetb
                  ) (BRAM_DUAL_PORT#(addr, data));

   let an <- vNullBRAMPort (clocked_by clka, reset_by reseta) ;
   let bn <- vNullBRAMPort (clocked_by clkb, reset_by resetb) ;

   return
   (interface  BRAM_DUAL_PORT
       interface  BRAM_PORT a = an;
       interface  BRAM_PORT b = bn;
   endinterface);
endmodule




//////////////////////////////////////////////
// Wrapper on the 2 port models
/////////////////////////////////////////////

module mkBRAMCore2#(
                    Integer memSize,
                    Bool hasOutputRegister
                   ) (BRAM_DUAL_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   (*hide*)
   let _ifc <- mkSyncBRAMCore2 (memSize, hasOutputRegister, clk, rst, clk, rst);
   return _ifc ;
endmodule



(* no_default_clock, no_default_reset *)
module mkSyncBRAMCore2#(Integer memSize,
                    Bool hasOutputRegister,
                    Clock clkA, Reset rstNA,
                    Clock clkB, Reset rstNB
                    ) (BRAM_DUAL_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
            );

   BRAM_DUAL_PORT#(addr, data) _ifc = ? ;
   if ( valueOf(data_sz) == 0 ) begin
      (*hide*)
      _ifc <- vNullBRAM2 (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB);
   end
   else if (valueOf(addr_sz) == 0) begin
      messageM ("Note: a Dual ported BRAM with Address size of 0 bits has been instantiated." +
                "This corresponds to a single register, with 2 write ports.");
      (*hide*)
      BRAM_DUAL_PORT#(Bit#(1), data) _x <- vSyncBRAM2 (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB);
      _ifc = (interface BRAM_DUAL_PORT;
                 interface BRAM_PORT a;
                    method Action put(Bool write, addr a, data d);
                       _x.a.put(write, 0, d);
                    endmethod
                    method data read = _x.a.read ;
                 endinterface
                 interface BRAM_PORT b;
                    method Action put(Bool write, addr a, data d);
                       _x.b.put(write, 0, d);
                    endmethod
                    method data read = _x.b.read ;
                 endinterface
              endinterface);
   end
   else begin
      (*hide*)
      _ifc  <- vSyncBRAM2 (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB);
   end
   return _ifc;
endmodule


//////////////////////////////////////////////////////////////////////
import "BVI" BRAM2Load =
module vSyncBRAM2Load#(Integer memSize,
                       Bool hasOutputRegister,
                       Clock clkA, Reset rstNA,
                       Clock clkB, Reset rstNB,
                       String file, Bool binary
                       ) (BRAM_DUAL_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
            );

   default_clock   no_clock;
   default_reset   no_reset;

   input_clock     clkA(CLKA, (*unused*)CLKA_GATE) = clkA;
   input_clock     clkB(CLKB, (*unused*)CLKB_GATE) = clkB;

   input_reset     rstA() = rstNA;
   input_reset     rstB() = rstNB;

   parameter FILENAME   = file;
   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));
   parameter BINARY     = Bit#(1) ' (pack(binary));

   interface BRAM_PORT a;
      method put(WEA, (* reg *)ADDRA, (* reg *)DIA) enable(ENA) clocked_by(clkA) reset_by(rstA);
      method DOA read() clocked_by(clkA) reset_by(rstA);
   endinterface: a

   interface BRAM_PORT b;
      method put(WEB, (* reg *)ADDRB, (* reg *)DIB) enable(ENB) clocked_by(clkB) reset_by(rstB);
      method DOB read() clocked_by(clkB) reset_by(rstB);
   endinterface: b
   schedule (a_read) CF (a_put, a_read);
   schedule a_put C a_put;
   schedule (b_read) CF (b_put, b_read);
   schedule b_put C b_put;
endmodule: vSyncBRAM2Load




module mkBRAMCore2Load#(
                        Integer memSize,
                        Bool hasOutputRegister,
                        String file, Bool binary
                       ) (BRAM_DUAL_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
           );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;

   (*hide*)
   let _i <- mkSyncBRAMCore2Load (memSize, hasOutputRegister,
                                  clk, rst, clk, rst,
                                  file, binary);
   return _i;
endmodule


(* no_default_clock, no_default_reset *)
module mkSyncBRAMCore2Load#(Integer memSize,
                        Bool hasOutputRegister,
                        Clock clkA, Reset rstNA,
                        Clock clkB, Reset rstNB,
                        String file, Bool binary
                        ) (BRAM_DUAL_PORT#(addr, data))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz)
            );

   BRAM_DUAL_PORT#(addr, data) _ifc = ? ;
   if ( valueOf(data_sz) == 0 ) begin
      (*hide*)
      _ifc <- vNullBRAM2(memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB) ;
   end
   else if (valueOf(addr_sz) == 0) begin
      messageM ("Note: a Dual ported BRAM with Address size of 0 bits has been instantiated." +
                "This corresponds to a single register, with 2 write ports.");
      (*hide*)
      BRAM_DUAL_PORT#(Bit#(1), data) _x <- vSyncBRAM2Load (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB, file, binary);
      _ifc = (interface BRAM_DUAL_PORT;
                 interface BRAM_PORT a;
                    method Action put(Bool write, addr a, data d);
                       _x.a.put(write, 0, d);
                    endmethod
                    method data read = _x.a.read ;
                 endinterface
                 interface BRAM_PORT b;
                    method Action put(Bool write, addr a, data d);
                       _x.b.put(write, 0, d);
                    endmethod
                    method data read = _x.b.read ;
                 endinterface
              endinterface);
   end
   else begin
      (*hide*)
      _ifc <- vSyncBRAM2Load(memSize, hasOutputRegister,
                             clkA, rstNA, clkB, rstNB,
                             file, binary);
   end
   return _ifc;
endmodule

////////////////////////////////////////////////////////////////////////////////
/// Dual Ported BRAM Byte Enabled Definition
////////////////////////////////////////////////////////////////////////////////
import "BVI" BRAM2BE =
module vSyncBRAM2BE#(
                     Integer memSize,
                     Bool hasOutputRegister,
                     Clock clkA, Reset rstNA, Clock clkB, Reset rstNB
                    ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   // This is currently a Bluesim limitation (can support 9-bit byte enables)
   if (valueof(chunk_sz) != 8)           error("Byte enables must control an 8-bit quantity.  You should adjust the width of your data, or the number of write enables.");
   // This is currently an XST limitation
   if (valueof(n) < 1 || valueof(n) > 4) warningM("XST will not infer a BRAM with fewer than 1 write enable or more than 4 write enables.");

   default_clock   no_clock;
   default_reset   no_reset;

   input_clock     clkA(CLKA, (*unused*)CLKA_GATE) = clkA;
   input_clock     clkB(CLKB, (*unused*)CLKB_GATE) = clkB;

   input_reset     rstA() = rstNA;
   input_reset     rstB() = rstNB;

   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter CHUNKSIZE  = valueof(chunk_sz);
   parameter WE_WIDTH   = valueof(n);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));

   interface BRAM_PORT_BE a;
      method put(WEA, (* reg *)ADDRA, (* reg *)DIA) enable(ENA) clocked_by(clkA) reset_by(rstA);
      method DOA read() clocked_by(clkA) reset_by(rstA);
   endinterface: a

   interface BRAM_PORT_BE b;
      method put(WEB, (* reg *)ADDRB, (* reg *)DIB) enable(ENB) clocked_by(clkB) reset_by(rstB);
      method DOB read() clocked_by(clkB) reset_by(rstB);
   endinterface: b
   schedule (a_read) CF (a_put, a_read);
   schedule a_put C a_put;
   schedule (b_read) CF (b_put, b_read);
   schedule b_put C b_put;
endmodule: vSyncBRAM2BE

module vNullBRAM2BE#(
                     Integer memSize, Bool hasOutputRegister,
                     Clock clka, Reset reseta,
                     Clock clkb, Reset resetb
                    ) (BRAM_DUAL_PORT_BE#(addr, data, n));

   let an <- vNullBRAMPortBE (clocked_by clka, reset_by reseta) ;
   let bn <- vNullBRAMPortBE (clocked_by clkb, reset_by resetb) ;

   return
   (interface  BRAM_DUAL_PORT_BE
       interface  BRAM_PORT_BE a = an;
       interface  BRAM_PORT_BE b = bn;
   endinterface);
endmodule


//////////////////////////////////////////////
// Wrapper on the 2 port models
/////////////////////////////////////////////

module mkBRAMCore2BE#(
                      Integer memSize,
                      Bool hasOutputRegister
                     ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   (*hide*)
   let _ifc <- mkSyncBRAMCore2BE (memSize, hasOutputRegister, clk, rst, clk, rst);
   return _ifc ;
endmodule



(* no_default_clock, no_default_reset *)
module mkSyncBRAMCore2BE#(
                          Integer memSize,
                          Bool hasOutputRegister,
                          Clock clkA, Reset rstNA,
                          Clock clkB, Reset rstNB
                         ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
            );

   BRAM_DUAL_PORT_BE#(addr, data, n) _ifc = ? ;
   if ( valueOf(data_sz) == 0 ) begin
      (*hide*)
      _ifc <- vNullBRAM2BE (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB);
   end
   else if (valueOf(addr_sz) == 0) begin
      messageM ("Note: a Dual ported BRAM with Address size of 0 bits has been instantiated." +
                "This corresponds to a single register, with 2 write ports.");
      (*hide*)
      BRAM_DUAL_PORT_BE#(Bit#(1), data, n) _x <- vSyncBRAM2BE (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB);
      _ifc = (interface BRAM_DUAL_PORT_BE;
                 interface BRAM_PORT_BE a;
                    method Action put(Bit#(n) writeen, addr a, data d);
                       _x.a.put(writeen, 0, d);
                    endmethod
                    method data read = _x.a.read ;
                 endinterface
                 interface BRAM_PORT_BE b;
                    method Action put(Bit#(n) writeen, addr a, data d);
                       _x.b.put(writeen, 0, d);
                    endmethod
                    method data read = _x.b.read ;
                 endinterface
              endinterface);
   end
   else begin
      (*hide*)
      _ifc  <- vSyncBRAM2BE (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB);
   end
   return _ifc;
endmodule


//////////////////////////////////////////////////////////////////////
import "BVI" BRAM2BELoad =
module vSyncBRAM2BELoad#(
                         Integer memSize,
                         Bool hasOutputRegister,
                         Clock clkA, Reset rstNA,
                         Clock clkB, Reset rstNB,
                         String file, Bool binary
                        ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   // This is currently a Bluesim limitation (can support 9-bit byte enables)
   if (valueof(chunk_sz) != 8)           error("Byte enables must control an 8-bit quantity.  You should adjust the width of your data, or the number of write enables.");
   // This is currently an XST limitation
   if (valueof(n) < 1 || valueof(n) > 4) warningM("XST will not infer a BRAM with fewer than 1 write enable or more than 4 write enables.");

   default_clock   no_clock;
   default_reset   no_reset;

   input_clock     clkA(CLKA, (*unused*)CLKA_GATE) = clkA;
   input_clock     clkB(CLKB, (*unused*)CLKB_GATE) = clkB;

   input_reset     rstA() = rstNA;
   input_reset     rstB() = rstNB;

   parameter FILENAME   = file;
   parameter PIPELINED  = Bit#(1) ' (pack(hasOutputRegister));
   parameter ADDR_WIDTH = valueof(addr_sz);
   parameter DATA_WIDTH = valueof(data_sz);
   parameter CHUNKSIZE  = valueof(chunk_sz);
   parameter WE_WIDTH   = valueof(n);
   parameter MEMSIZE    = Bit#(TAdd#(1,addr_sz)) ' (fromInteger(memSize));
   parameter BINARY     = Bit#(1) ' (pack(binary));

   interface BRAM_PORT_BE a;
      method put(WEA, (* reg *)ADDRA, (* reg *)DIA) enable(ENA) clocked_by(clkA) reset_by(rstA);
      method DOA read() clocked_by(clkA) reset_by(rstA);
   endinterface: a

   interface BRAM_PORT_BE b;
      method put(WEB, (* reg *)ADDRB, (* reg *)DIB) enable(ENB) clocked_by(clkB) reset_by(rstB);
      method DOB read() clocked_by(clkB) reset_by(rstB);
   endinterface: b
   schedule (a_read) CF (a_put, a_read);
   schedule a_put C a_put;
   schedule (b_read) CF (b_put, b_read);
   schedule b_put C b_put;
endmodule: vSyncBRAM2BELoad




module mkBRAMCore2BELoad#(
                          Integer memSize,
                          Bool hasOutputRegister,
                          String file, Bool binary
                         ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
           );

   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;

   (*hide*)
   let _i <- mkSyncBRAMCore2BELoad (memSize, hasOutputRegister,
                                    clk, rst, clk, rst,
                                    file, binary);
   return _i;
endmodule


(* no_default_clock, no_default_reset *)
module mkSyncBRAMCore2BELoad#(
                              Integer memSize,
                              Bool hasOutputRegister,
                              Clock clkA, Reset rstNA,
                              Clock clkB, Reset rstNB,
                              String file, Bool binary
                             ) (BRAM_DUAL_PORT_BE#(addr, data, n))
   provisos(
            Bits#(addr, addr_sz),
            Bits#(data, data_sz),
            Div#(data_sz, n, chunk_sz),
            Mul#(chunk_sz, n, data_sz)
            );

   BRAM_DUAL_PORT_BE#(addr, data, n) _ifc = ? ;
   if ( valueOf(data_sz) == 0 ) begin
      (*hide*)
      _ifc <- vNullBRAM2BE(memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB) ;
   end
   else if (valueOf(addr_sz) == 0) begin
      messageM ("Note: a Dual ported BRAM with Address size of 0 bits has been instantiated." +
                "This corresponds to a single register, with 2 write ports.");
      (*hide*)
      BRAM_DUAL_PORT_BE#(Bit#(1), data, n) _x <- vSyncBRAM2BELoad (memSize, hasOutputRegister, clkA, rstNA, clkB, rstNB, file, binary);
      _ifc = (interface BRAM_DUAL_PORT_BE;
                 interface BRAM_PORT_BE a;
                    method Action put(Bit#(n) writeen, addr a, data d);
                       _x.a.put(writeen, 0, d);
                    endmethod
                    method data read = _x.a.read ;
                 endinterface
                 interface BRAM_PORT_BE b;
                    method Action put(Bit#(n) writeen, addr a, data d);
                       _x.b.put(writeen, 0, d);
                    endmethod
                    method data read = _x.b.read ;
                 endinterface
              endinterface);
   end
   else begin
      (*hide*)
      _ifc <- vSyncBRAM2BELoad(memSize, hasOutputRegister,
                               clkA, rstNA, clkB, rstNB,
                               file, binary);
   end
   return _ifc;
endmodule

endpackage
