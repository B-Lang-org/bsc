
`ifdef BSV_ASSIGNMENT_DELAY
`else
 `define BSV_ASSIGNMENT_DELAY
`endif

// Single-Ported BRAM with byte enables and ability to load from file
module BRAM1BELoad(CLK,
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
   parameter                      CHUNKSIZE  = 1;
   parameter                      WE_WIDTH   = 1;
   parameter                      MEMSIZE    = 1;
   parameter                      BINARY     = 0;

   input                          CLK;
   input                          EN;
   input [WE_WIDTH-1:0]           WE;
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

   // iverilog does not support the full verilog-2001 language.  This fixes that for simulation.
`ifdef __ICARUS__
   reg [DATA_WIDTH-1:0]  MASK, IMASK;
   reg [DATA_WIDTH-1:0]  DATA;
   wire [DATA_WIDTH-1:0] DATAwr;

   assign DATAwr = RAM[ADDR] ;


   always @(WE or DI or DATAwr) begin : combo1
      integer j;
      MASK  = 0;
      IMASK = 0;

      for(j = WE_WIDTH-1; j >= 0; j = j - 1) begin
         if (WE[j]) MASK = (MASK << 8) | { { DATA_WIDTH-CHUNKSIZE { 1'b0 } }, { CHUNKSIZE { 1'b1 } } };
         else       MASK = (MASK << 8);
      end
      IMASK = ~MASK;

      DATA = (DATAwr & IMASK) | (DI & MASK);
   end

   
   always @(posedge CLK) begin
      if (EN) begin
         if (WE) begin
            RAM[ADDR] <= `BSV_ASSIGNMENT_DELAY DATA;
            DO_R      <= `BSV_ASSIGNMENT_DELAY DATA;
         end
         else begin
            DO_R      <= `BSV_ASSIGNMENT_DELAY RAM[ADDR];
         end
      end
   end
`else
   generate
      genvar i;
      for(i = 0; i < WE_WIDTH; i = i + 1) begin: porta_we
         always @(posedge CLK) begin
            if (EN) begin
               if (WE[i]) begin
                  RAM[ADDR][((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE] <= `BSV_ASSIGNMENT_DELAY DI[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE];
                  DO_R[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE]      <= `BSV_ASSIGNMENT_DELAY DI[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE];
               end
               else begin
                  DO_R[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE]      <= `BSV_ASSIGNMENT_DELAY RAM[ADDR][((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE];
               end
            end
         end
      end      
   endgenerate
`endif // !`ifdef __ICARUS__

   // Output driver
   always @(posedge CLK) begin
      DO_R2 <= `BSV_ASSIGNMENT_DELAY DO_R;
   end
   
   assign DO = (PIPELINED) ? DO_R2 : DO_R;

endmodule // BRAM1BELoad
