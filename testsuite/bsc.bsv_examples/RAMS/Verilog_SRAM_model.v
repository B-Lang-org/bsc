// ----------------------------------------------------------------
// This is an example Verilog SRAM model that we import into the
// the Bluespec SystemVerilog (BSV) environment.

// The behavior of this module is very simple:
// A memory request is made only when v_in_enable is asserted
//
//     If v_in_write_not_read is true, it is a write request, and
//         v_in_address and v_in_data supply the address and data
//
//     If v_in_write_not_read is false, it is a read request, and
//         v_in_address supplies the address (v_in_data is ignored)
//
// v_out_data always produces the memory contents of the most recently
// supplied address, whether for read or for write.  There is a 1-cycle
// latency from a request until when the corresponding v_out_data is available
//
// Requests can be supplied on every cycle, i.e., the memory is pipelined.
//
// The memory is initialized to the data in FILENAME, at start of simulation
// Data must be supplied in standard Verilog $readmemh hex format

// It is quite easy to modify this example for other RAM models
// ----------------------------------------------------------------

module mkVerilog_SRAM_model (clk,
                             v_in_address, v_in_data, v_in_write_not_read, v_in_enable,
                             v_out_data);

  parameter FILENAME      = "Verilog_SRAM_model.data";
  parameter ADDRESS_WIDTH = 10;
  parameter DATA_WIDTH    = 8;
  parameter NWORDS        = (1 << ADDRESS_WIDTH);

  input                       clk;
  input  [ADDRESS_WIDTH-1:0]  v_in_address;
  input  [DATA_WIDTH-1:0]     v_in_data;
  input                       v_in_write_not_read;
  input                       v_in_enable;

  output [DATA_WIDTH-1:0]     v_out_data;

  reg    [DATA_WIDTH-1:0]     memory [NWORDS-1:0];
  reg    [ADDRESS_WIDTH-1:0]  address_reg;
  reg    [DATA_WIDTH-1:0]     in_data_reg;
  reg                         write_not_read_reg;

  // synopsys translate_off
  initial    $readmemh (FILENAME, memory);
  // synopsys translate_on

  assign v_out_data =  memory[address_reg];

  always@(posedge clk)
  begin
    if (v_in_enable) begin
      address_reg         <= v_in_address;
      in_data_reg         <= v_in_data;
      write_not_read_reg  <= v_in_write_not_read;
    end
    else
      write_not_read_reg  <= 0;

    if (write_not_read_reg)
      memory[address_reg] <= in_data_reg;
  end
  
endmodule
