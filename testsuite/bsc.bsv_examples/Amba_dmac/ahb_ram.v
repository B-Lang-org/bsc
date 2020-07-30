//------------------------------------------------------------------------------
//
//  FILENAME:ahb_ram.v
//
//  DESCRIPTION: 
//     amba ahb internal sram.
//
//------------------------------------------------------------------------------
// 
//
//

//`timescale 1 ns / 10 ps         

                                
module ahb_ram(
   hclk,      // input         
   hresetn,   // input         
   hsel,      // input         
   hready,    // input         
   hwrite,    // input         
   htrans,    // input   [1:0] 
   haddr,     // input  [31:0] 
   hwdata,    // input  [31:0] 
   hreadyout, // output        
   hresp,     // output  [1:0] 
   hrdata);   // output [31:0] 

   input         hclk;     
   input         hresetn;  
   input         hsel;     
   input         hready;   
   input         hwrite;   
   input   [1:0] htrans;   
   input  [31:0] haddr;    
   input  [31:0] hwdata;   
   output        hreadyout;
   output  [1:0] hresp;    
   output [31:0] hrdata;   

   reg           cs;
   reg           we;
   reg    [11:0] addr;

   assign  hreadyout = 1'b1;  // Always return hready (zero wait-state)
   assign  hresp     = 2'b00; // 0-ws, always ok (never error)    

   always @(posedge hclk or negedge hresetn) begin
      if (!hresetn) begin
         cs   <= 1'b0;
         we   <= 1'b0;
         addr <= 10'h0; 
      end
      else begin
         cs   <= hsel && (htrans>2'b1) && hready;
         we   <= hsel && (htrans>2'b1) && hready && hwrite;
         addr <= haddr; 
      end
   end


   ram_1024x32 u_ram (
     .clk   (hclk),
     .cs    (cs),  // cs=0 puts ram into low-power mode
     .we    (we),            
     .addr  (addr[11:2]),                                       
     .wdata (hwdata),                                        
     .rdata (hrdata) );                                     

endmodule // module ahb_ram
