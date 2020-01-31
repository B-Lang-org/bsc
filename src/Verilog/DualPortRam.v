
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

// A dual port RAM model 
// this model has synchronous Write port and an
// asynchronous read port. 
//  Hence the read can be on different clock than the write port
module DualPortRam(
                   CLK,         // write clock
                   WE, 
                   WADDR, 
                   DIN,
                   RADDR, 
                   DOUT
                   );

   parameter addrWidth = 5;        // number of bits in address-bus
   parameter dataWidth = 16;       // number of bits in data-bus

   // write port
   input                  CLK;             // write clock
   
   input                  WE;              // write enable (active high)
   input [addrWidth-1:0]  WADDR;    // write address
   input [dataWidth-1:0]  DIN;      // data input

   // read port
   input [addrWidth-1:0] RADDR;   // read address
   output [dataWidth-1:0] DOUT;    // data output

   
   reg [dataWidth-1:0]    memArray [(1<<addrWidth) -1:0] ;

   // read operation -- combinational operation
   assign                 DOUT = memArray[RADDR];

   // write operation
   always @(posedge CLK)
      begin
         if (WE)
            begin
               memArray[WADDR] <= `BSV_ASSIGNMENT_DELAY DIN;
            end
      end // always @ (posedge WCLK)
   
   
`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial
     begin : init_block
        integer          i; 		// temporary for generate reset value
        for (i = 0; i < (1<<addrWidth); i = i + 1)
          begin
             memArray[i] = {((dataWidth + 1)/2){2'b10}} ;
          end 
     end // initial begin   
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule


