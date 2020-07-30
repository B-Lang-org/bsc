//------------------------------------------------------------------------------
//
//  FILENAME:ram_1024x32.v
//
//  DESCRIPTION: 
//    synchronous 1024x32 sram
//
//------------------------------------------------------------------------------
// 
//
//

module ram_1024x32 (
   clk,                    // input
   cs,                     // input
   we,                     // input
   addr,                   // input  [9:0]
   wdata,                  // input  [31:0] write data (din)
   rdata);                 // output [31:0] read data (dout)

   input         clk;      //
   input         cs;       //
   input         we;       //
   input   [9:0] addr;     //
   input  [31:0] wdata;    // write data (din)
   output [31:0] rdata;    // read data (dout)

   reg [31:0] mem[0:1023];
   reg [31:0] dout;

   // ram is in low-power mode when cs=0 and rdata remains constant
   assign rdata = cs ? mem[addr] : dout;

   always @(posedge clk) begin
      if (cs) dout <= mem[addr];
      if (cs && we) begin
         mem[addr] <= wdata;
      end
   end

endmodule
