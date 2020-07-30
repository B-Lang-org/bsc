// Example to show how to wrap a Verilog SRAM module and make it
// available to Bluespec SystemVerilog programs

package SRAM_wrapper;

// ----------------------------------------------------------------
// Interface to the Verilog SRAM, as seen by BSV clients

interface SRAM_Ifc #( type addr_t, type data_t );
   method Action  request ( addr_t address,
                            data_t data,
                            Bool write_not_read );
   method data_t  read_response;
endinterface: SRAM_Ifc

// ----------------------------------------------------------------
// Import the Verilog module, and let it have an SRAM_Ifc interface
// See Section 15 of Reference Guide for syntax and semantics

import "BVI" mkVerilog_SRAM_model =
   module mkSRAM #(String filename) (SRAM_Ifc #(addr_t, data_t))
    provisos(Bits#(addr_t, addr_width),
             Bits#(data_t, data_width));

      // Parameters passed to the Verilog model
      parameter FILENAME      = filename;
      parameter ADDRESS_WIDTH = valueOf(addr_width);
      parameter DATA_WIDTH    = valueof(data_width);

      // Default clk and no reset passed to the Verilog model
      default_clock clk(clk);
      no_reset;

      // Verilog ports corresponding to method args, results and controls
      method             request (v_in_address, v_in_data, v_in_write_not_read)
                                 enable (v_in_enable);
      method v_out_data  read_response;

      // Both methods can be called in the same clock,
      // but read_response must logically precede request
      schedule (read_response) SB (request);

      // The response can be read by multiple rules in a clock cycle
      schedule (read_response) CF (read_response);
      // A request can only be made once in a clock cycle
      schedule (request) C (request);
   endmodule  

// ----------------------------------------------------------------

endpackage: SRAM_wrapper
