// Example testbench exercising the wrapped/imported Verilog SRAM module

package Test;

import StmtFSM      :: *;
import SRAM_wrapper :: *;

typedef Bit#(5)  A5;
typedef Bit#(32) D32;

typedef enum { Reading1, Writing, Reading2, Done } TestState
        deriving (Bits, Eq);

(* synthesize *)
module mkTop (Empty);

   // Show cycles, just for information
   Reg#(int) cycle <- mkReg(0);
   rule show_cycles;
      $display ("Cycle %d ----------------------------------", cycle);
      cycle <= cycle + 1;
   endrule

   // SRAM instantiation
   SRAM_Ifc#(A5, D32) sram_5_32 <- mkSRAM("mem_init.data");

   Reg#(TestState) state <- mkReg (Reading1);
   Reg#(A5)        addr  <- mkReg(0);

   // Read all locations and print data (initial memory values)
   // Remember that response data arrives 1 cycle after sending a read request
   rule read_data_1 (state == Reading1);
      if (addr > 0) begin
         $display("    ==> %h", sram_5_32.read_response());
      end

      $display("Read [%h]", addr);
      sram_5_32.request (addr, ?, False);

      if (addr == maxBound)
         state <= Writing;
      addr <= addr + 1;
   endrule

   // Overwrite all locations with known values
   rule write_data (state == Writing);
      if (addr == 0) begin
         $display("    ==> %h", sram_5_32.read_response());
      end

      D32 data = (zeroExtend (addr) << 4);
      $display("Write [%h] = %h ", addr, data);
      sram_5_32.request (addr, data, True);
      if (addr == maxBound) begin
         addr <= 0;
         state <= Reading2;
      end
      else
         addr <= addr + 1;
   endrule

   // Read all locations and print data (new memory values)
   rule read_data_2 (state == Reading2);
      if (addr > 0) begin
         $display("    ==> %h", sram_5_32.read_response());
      end

      $display("Read [%h]", addr);
      sram_5_32.request (addr, ?, False);

      if (addr == maxBound)
         state <= Done;
      addr <= addr + 1;
   endrule

   rule done (state == Done);
      $display("    ==> %h", sram_5_32.read_response());
      $finish(0);
   endrule

endmodule: mkTop

endpackage: Test
