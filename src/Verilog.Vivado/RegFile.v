
`ifdef  BSV_WARN_REGFILE_ADDR_RANGE
`else
`define BSV_WARN_REGFILE_ADDR_RANGE 0 
`endif


`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif


// Multi-ported Register File
module RegFile(CLK,
               ADDR_IN, D_IN, WE,
               ADDR_1, D_OUT_1,
               ADDR_2, D_OUT_2,
               ADDR_3, D_OUT_3,
               ADDR_4, D_OUT_4,
               ADDR_5, D_OUT_5
               );
   parameter                   addr_width = 1;
   parameter                   data_width = 1;
   parameter                   lo = 0;
   parameter                   hi = 1;

   input                       CLK;
   input [addr_width - 1 : 0]  ADDR_IN;
   input [data_width - 1 : 0]  D_IN;
   input                       WE;

   input [addr_width - 1 : 0]  ADDR_1;
   output [data_width - 1 : 0] D_OUT_1;

   input [addr_width - 1 : 0]  ADDR_2;
   output [data_width - 1 : 0] D_OUT_2;

   input [addr_width - 1 : 0]  ADDR_3;
   output [data_width - 1 : 0] D_OUT_3;

   input [addr_width - 1 : 0]  ADDR_4;
   output [data_width - 1 : 0] D_OUT_4;

   input [addr_width - 1 : 0]  ADDR_5;
   output [data_width - 1 : 0] D_OUT_5;

   (* RAM_STYLE = "DISTRIBUTED" *)
   reg [data_width - 1 : 0]    arr[lo:hi];


`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
`ifndef SYNTHESIS
   initial
     begin : init_block
        integer                     i;          // temporary for generate reset value
        for (i = lo; i <= hi; i = i + 1) begin
           arr[i] = {((data_width + 1)/2){2'b10}} ;
        end
     end // initial begin
`endif // SYNTHESIS
`endif // BSV_NO_INITIAL_BLOCKS


   always@(posedge CLK)
     begin
        if (WE)
          arr[ADDR_IN] <= `BSV_ASSIGNMENT_DELAY D_IN;
     end // always@ (posedge CLK)

   assign D_OUT_1 = arr[ADDR_1];
   assign D_OUT_2 = arr[ADDR_2];
   assign D_OUT_3 = arr[ADDR_3];
   assign D_OUT_4 = arr[ADDR_4];
   assign D_OUT_5 = arr[ADDR_5];

`ifndef SYNTHESIS
   always@(posedge CLK)
     begin : runtime_check
        reg enable_check;
        enable_check = `BSV_WARN_REGFILE_ADDR_RANGE ;
        if ( enable_check )
           begin
              if (( ADDR_1 < lo ) || (ADDR_1 > hi) )
                $display( "Warning: RegFile: %m -- Address port 1 is out of bounds: %h", ADDR_1 ) ;
              if (( ADDR_2 < lo ) || (ADDR_2 > hi) )
                $display( "Warning: RegFile: %m -- Address port 2 is out of bounds: %h", ADDR_2 ) ;
              if (( ADDR_3 < lo ) || (ADDR_3 > hi) )
                $display( "Warning: RegFile: %m -- Address port 3 is out of bounds: %h", ADDR_3 ) ;
              if (( ADDR_4 < lo ) || (ADDR_4 > hi) )
                $display( "Warning: RegFile: %m -- Address port 4 is out of bounds: %h", ADDR_4 ) ;
              if (( ADDR_5 < lo ) || (ADDR_5 > hi) )
                $display( "Warning: RegFile: %m -- Address port 5 is out of bounds: %h", ADDR_5 ) ;
              if ( WE && ( ADDR_IN < lo ) || (ADDR_IN > hi) )
                $display( "Warning: RegFile: %m -- Write Address port is out of bounds: %h", ADDR_IN ) ;
           end
     end
`endif // SYNTHESIS

endmodule
