package ExtSDRAM;

// This packages is a simple model for the external synchronous DRAM; it is
// used by the testbench to store the lookup table.

import ConfigReg::*;
import RegFile::*;
import RegFile::*;
import SDRAM::*;

import ShiftRegisters::*;

// This module takes as an argument the interface provided by its wrapper; its
// own interface is empty:
module mkExtSDRAM(ExtSDRAM ifc, Empty provided_ifc);

   // The data items are store in an "ArrayFile", an object similar to a
   // register file, from the BSV library:
   RegFile#(Bit#(AddrSize), Bit#(DataSize)) rom() ;
   mkRegFileLoad#("SRAM.handbuilt", 0, 'h1fffff) rom_inst(rom) ;

   // To increase the latency:
   ShiftReg#(Bit#(DataSize)) buff();
   mkShifter#(2) the_buff(buff);

   // On every cycle, any request coming in on the request wires (ifc.rd and
   // ifc.wr) is handled, and the output placed in the shift register.  The
   // attribute checks that the rule will fire on every cycle:
   (* no_implicit_conditions, fire_when_enabled *)
   rule every;
      action
	 if (ifc.rd && !ifc.wr)
	    buff.sin(Valid(rom.sub(ifc.addr)));
	 else 
	    buff.sin(Invalid);
	 ifc.dOut(buff.sout);
      endaction
   endrule
   
endmodule

endpackage
