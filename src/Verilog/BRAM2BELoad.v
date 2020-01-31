
`ifdef BSV_ASSIGNMENT_DELAY
`else
 `define BSV_ASSIGNMENT_DELAY
`endif

// Dual-Ported BRAM (WRITE FIRST) with byte enables and ability to load from a file
module BRAM2BELoad(CLKA,
                   ENA,
                   WEA,
                   ADDRA,
                   DIA,
                   DOA,
                   CLKB,
                   ENB,
                   WEB,
                   ADDRB,
                   DIB,
                   DOB
                  );

   parameter                      FILENAME   = "";
   parameter                      PIPELINED  = 0;
   parameter                      ADDR_WIDTH = 1;
   parameter                      DATA_WIDTH = 1;
   parameter                      CHUNKSIZE  = 1;
   parameter                      WE_WIDTH   = 1;
   parameter                      MEMSIZE    = 1;
   parameter                      BINARY     = 0;

   input                          CLKA;
   input                          ENA;
   input [WE_WIDTH-1:0]           WEA;
   input [ADDR_WIDTH-1:0]         ADDRA;
   input [DATA_WIDTH-1:0]         DIA;
   output [DATA_WIDTH-1:0]        DOA;

   input                          CLKB;
   input                          ENB;
   input [WE_WIDTH-1:0]           WEB;
   input [ADDR_WIDTH-1:0]         ADDRB;
   input [DATA_WIDTH-1:0]         DIB;
   output [DATA_WIDTH-1:0]        DOB;

   reg [DATA_WIDTH-1:0]           RAM[0:MEMSIZE-1] /* synthesis syn_ramstyle="no_rw_check" */ ;
   reg [DATA_WIDTH-1:0]           DOA_R;
   reg [DATA_WIDTH-1:0]           DOA_R2;
   reg [DATA_WIDTH-1:0]           DOB_R;
   reg [DATA_WIDTH-1:0]           DOB_R2;

   // synopsys translate_off
   initial
   begin : init_block
`ifdef BSV_NO_INITIAL_BLOCKS
`else
      DOA_R  = { ((DATA_WIDTH+1)/2) { 2'b10 } };
      DOA_R2 = { ((DATA_WIDTH+1)/2) { 2'b10 } };
      DOB_R  = { ((DATA_WIDTH+1)/2) { 2'b10 } };
      DOB_R2 = { ((DATA_WIDTH+1)/2) { 2'b10 } };
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
   
   // PORT A

   // iverilog does not support the full verilog-2001 language.  This fixes that for simulation.
`ifdef __ICARUS__
   reg [DATA_WIDTH-1:0]  MASKA, IMASKA;
   reg  [DATA_WIDTH-1:0] DATA_A;
   wire [DATA_WIDTH-1:0] DATA_Awr;

   assign DATA_Awr = RAM[ADDRA];

   always @(WEA or DIA or DATA_Awr) begin : combo1
      integer j;
      MASKA  = 0;
      IMASKA = 0;

      for(j = WE_WIDTH-1; j >= 0; j = j - 1) begin
         if (WEA[j]) MASKA = (MASKA << 8) | { { DATA_WIDTH-CHUNKSIZE { 1'b0 } }, { CHUNKSIZE { 1'b1 } } };
         else        MASKA = (MASKA << 8);
      end
      IMASKA = ~MASKA;

      DATA_A = (DATA_Awr & IMASKA) | (DIA & MASKA);
   end

   always @(posedge CLKA) begin
      if (ENA) begin
         if (WEA) begin
            RAM[ADDRA] <= `BSV_ASSIGNMENT_DELAY DATA_A;
            DOA_R      <= `BSV_ASSIGNMENT_DELAY DATA_A;
         end
         else begin
            DOA_R      <= `BSV_ASSIGNMENT_DELAY RAM[ADDRA];
         end
      end
   end
`else
   generate
      genvar i;
      for(i = 0; i < WE_WIDTH; i = i + 1) begin: porta_we
         always @(posedge CLKA) begin
            if (ENA) begin
               if (WEA[i]) begin
                  RAM[ADDRA][((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE] <= `BSV_ASSIGNMENT_DELAY DIA[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE];
                  DOA_R[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE]      <= `BSV_ASSIGNMENT_DELAY DIA[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE];
               end
               else begin
                  DOA_R[((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE]      <= `BSV_ASSIGNMENT_DELAY RAM[ADDRA][((i+1)*CHUNKSIZE)-1 : i*CHUNKSIZE];
               end
            end
         end
      end
   endgenerate
`endif // !`ifdef __ICARUS__

   // PORT B

   // iverilog does not support the full verilog-2001 language.  This fixes that for simulation.
`ifdef __ICARUS__
   reg [DATA_WIDTH-1:0]  MASKB, IMASKB;
   reg  [DATA_WIDTH-1:0] DATA_B;
   wire [DATA_WIDTH-1:0] DATA_Bwr;

   assign DATA_Bwr = RAM[ADDRB];

   always @(WEB or DIB or DATA_Bwr) begin : combo2
      integer j;
      MASKB  = 0;
      IMASKB = 0;

      for(j = WE_WIDTH-1; j >= 0; j = j - 1) begin
         if (WEB[j]) MASKB = (MASKB << 8) | { { DATA_WIDTH-CHUNKSIZE { 1'b0 } }, { CHUNKSIZE { 1'b1 } } };
         else        MASKB = (MASKB << 8);
      end
      IMASKB = ~MASKB;

      DATA_B = (DATA_Bwr & IMASKB) | (DIB & MASKB);
   end

   always @(posedge CLKB) begin
      if (ENB) begin
         if (WEB) begin
            RAM[ADDRB] <= `BSV_ASSIGNMENT_DELAY DATA_B;
            DOB_R      <= `BSV_ASSIGNMENT_DELAY DATA_B;
         end
         else begin
            DOB_R      <= `BSV_ASSIGNMENT_DELAY RAM[ADDRB];
         end
      end
   end
`else
   generate
      genvar k;
      for(k = 0; k < WE_WIDTH; k = k + 1) begin: portb_we
         always @(posedge CLKB) begin
            if (ENB) begin
               if (WEB[k]) begin
                  RAM[ADDRB][((k+1)*CHUNKSIZE)-1 : k*CHUNKSIZE] <= `BSV_ASSIGNMENT_DELAY DIB[((k+1)*CHUNKSIZE)-1 : k*CHUNKSIZE];
                  DOB_R[((k+1)*CHUNKSIZE)-1 : k*CHUNKSIZE]      <= `BSV_ASSIGNMENT_DELAY DIB[((k+1)*CHUNKSIZE)-1 : k*CHUNKSIZE];
               end
               else begin
                  DOB_R[((k+1)*CHUNKSIZE)-1 : k*CHUNKSIZE]      <= `BSV_ASSIGNMENT_DELAY RAM[ADDRB][((k+1)*CHUNKSIZE)-1 : k*CHUNKSIZE];
               end
            end
         end
      end
   endgenerate
`endif // !`ifdef __ICARUS__

   // Output drivers
   always @(posedge CLKA) begin
      DOA_R2 <= `BSV_ASSIGNMENT_DELAY DOA_R;
   end

   always @(posedge CLKB) begin
      DOB_R2 <= `BSV_ASSIGNMENT_DELAY DOB_R;
   end

   assign DOA = (PIPELINED) ? DOA_R2 : DOA_R;
   assign DOB = (PIPELINED) ? DOB_R2 : DOB_R;

endmodule // BRAM2BELoad
