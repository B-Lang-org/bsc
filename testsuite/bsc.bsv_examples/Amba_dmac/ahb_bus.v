//------------------------------------------------------------------------------
//
//  FILENAME: ahb_bus.v
//
//  DESCRIPTION: 
//     amba ahb bus. Supports 1 master, 4 slaves and a default (error) slave.
//
//------------------------------------------------------------------------------
// 
//
//

//`timescale 1ns/10ps
module ahb_bus(
   hclk,           // input
   hresetn,        // input

   // Master Interface

   haddr_31_28,    // input   [3:0]
   hrdata,         // output [31:0] 
   hready,         // output        
   hresp,          // output  [1:0]  

   // Slave Interfaces

   hsel0,          // output
   hrdata0,        // input  [31:0] 
   hready0,        // input         
   hresp0,         // input   [1:0]  

   hsel1,          // output
   hrdata1,        // input  [31:0] 
   hready1,        // input         
   hresp1,         // input   [1:0]  

   hsel2,          // output
   hrdata2,        // input  [31:0] 
   hready2,        // input         
   hresp2,         // input   [1:0]  

   hsel3,          // output
   hrdata3,        // input  [31:0] 
   hready3,        // input         
   hresp3,         // input   [1:0]  

   hseldefault,    // output
   hrdatadefault,  // input  [31:0] 
   hreadydefault,  // input         
   hrespdefault);  // input   [1:0]  


   input          hclk;            
   input          hresetn;         

   // Master Interface

   input   [3:0]  haddr_31_28;     
   output [31:0]  hrdata;          
   output         hready;          
   output  [1:0]  hresp;             

   // Slave Interfaces

   output         hsel0;           
   input  [31:0]  hrdata0;         
   input          hready0;         
   input   [1:0]  hresp0;           

   output         hsel1;           
   input  [31:0]  hrdata1;         
   input          hready1;         
   input   [1:0]  hresp1;           

   output         hsel2;           
   input  [31:0]  hrdata2;         
   input          hready2;         
   input   [1:0]  hresp2;           

   output         hsel3;           
   input  [31:0]  hrdata3;         
   input          hready3;         
   input   [1:0]  hresp3;           

   output         hseldefault;     
   input  [31:0]  hrdatadefault;   
   input          hreadydefault;   
   input   [1:0]  hrespdefault;    


   reg     [3:0] haddr_31_28_r;

   // The following reg's are combinatorial
   reg    [31:0] hrdata;    
   reg           hready;    
   reg     [1:0] hresp;     


   assign hsel0 = (haddr_31_28 == 4'h0);
   assign hsel1 = (haddr_31_28 == 4'h1);
   assign hsel2 = (haddr_31_28 == 4'h2);
   assign hsel3 = (haddr_31_28 == 4'h3);
   assign hseldefault = (haddr_31_28 > 4'h3);


   always @ (posedge hclk or negedge hresetn) begin
      if (!hresetn) begin
        haddr_31_28_r <= 4'hF;
      end
      else begin
         if (hready) begin // only update when hready is high
            if (haddr_31_28<4'h4)
               haddr_31_28_r <= haddr_31_28; // simple decode, custom for each design
            else begin
               haddr_31_28_r <= 4'hF; // default slave
            end
         end
      end
   end

   // Combinatorial always block

   always @(haddr_31_28_r or 
            hrdata0 or hrdata1 or hrdata2 or hrdata3 or hrdatadefault or
            hready0 or hready1 or hready2 or hready3 or hreadydefault or 
            hresp0 or hresp1 or hresp2 or hresp3 or hrespdefault)
   begin
      case (haddr_31_28_r[3:0]) 
         4'h0: begin
               hrdata = hrdata0;
               hready = hready0;
               hresp  = hresp0;
               end
         4'h1: begin
               hrdata = hrdata1;
               hready = hready1;
               hresp  = hresp1;
               end
         4'h2: begin
               hrdata = hrdata2;
               hready = hready2;
               hresp  = hresp2;
               end
         4'h3: begin
               hrdata = hrdata3;
               hready = hready3;
               hresp  = hresp3;
               end
         default: begin
               hrdata = hrdatadefault;
               hready = hreadydefault;
               hresp  = hrespdefault;
               end
      endcase
   end

endmodule	
