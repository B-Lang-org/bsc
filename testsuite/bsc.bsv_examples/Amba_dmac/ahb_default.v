//------------------------------------------------------------------------------
//
//  FILENAME: ahb_default.v
//
//  DESCRIPTION: 
//    amba ahb default slave.
//
//------------------------------------------------------------------------------
// 
//
//

//`timescale 1ns/1ps

module ahb_default (
   hclk,        // input
   hresetn,     // input
   hready,      // input
   hsel,        // input
   htrans,      // input [1:0]
   hreadyout,   // output
   hresp);      // output [1:0]

   input        hclk;
   input        hresetn;
   input        hready;
   input        hsel;
   input  [1:0] htrans;
   output       hreadyout;
   output [1:0] hresp;

   reg    [1:0] hresp;
   reg          hreadyout;

   wire         transfer_attempt;
   assign       transfer_attempt = hready && hsel && (htrans >2'b01);

   always @(posedge hclk or negedge hresetn) begin
      if (!hresetn) begin
         hreadyout <= 1'b1;
         hresp <= 2'b00;
      end
      else begin
         hreadyout <= !hreadyout || !transfer_attempt;
         if (hreadyout) begin
            hresp <= transfer_attempt ? 2'b01 : 2'b00;
         end
      end
   end

endmodule
