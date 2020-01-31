
`ifdef BSV_ASSIGNMENT_DELAY
`else
 `define BSV_ASSIGNMENT_DELAY
`endif

// Single-Ported BRAM
module BRAM1Load(CLK,
                 EN,
                 WE,
                 ADDR,
                 DI,
                 DO
                 );

   parameter                      FILENAME   = "";
   parameter                      PIPELINED  = 0;
   parameter                      ADDR_WIDTH = 1;
   parameter                      DATA_WIDTH = 1;
   parameter                      MEMSIZE    = 1;
   parameter                      BINARY     = 0;

   input                          CLK;
   input                          EN;
   input                          WE;
   input [ADDR_WIDTH-1:0]         ADDR;
   input [DATA_WIDTH-1:0]         DI;
   output [DATA_WIDTH-1:0]        DO;

   reg [DATA_WIDTH-1:0]           RAM[0:MEMSIZE-1];
   reg [DATA_WIDTH-1:0]           DO_R;
   reg [DATA_WIDTH-1:0]           DO_R2;

   // synopsys translate_off
   initial
   begin : init_block
`ifdef BSV_NO_INITIAL_BLOCKS
`else
      DO_R  = { ((DATA_WIDTH+1)/2) { 2'b10 } };
      DO_R2 = { ((DATA_WIDTH+1)/2) { 2'b10 } };
`endif // !`ifdef BSV_NO_INITIAL_BLOCKS
   end
   // synopsys translate_on

   initial
   begin : init_rom_block
      if (BINARY)
        $readmemb(FILENAME, RAM, 0, MEMSIZE-1);
      else
        $readmemh(FILENAME, RAM, 0, MEMSIZE-1);
   end

   always @(posedge CLK) begin
      if (EN) begin
         if (WE) begin
            RAM[ADDR] <= `BSV_ASSIGNMENT_DELAY DI;
            DO_R <= `BSV_ASSIGNMENT_DELAY DI;
         end
         else begin
            DO_R <= `BSV_ASSIGNMENT_DELAY RAM[ADDR];
         end
      end
      DO_R2 <= `BSV_ASSIGNMENT_DELAY DO_R;
   end

   // Output driver
   assign DO = (PIPELINED) ? DO_R2 : DO_R;

endmodule // BRAM1Load
