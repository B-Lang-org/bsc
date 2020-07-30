//
// Generate reset signal.
// If the keyboard data is low for about 0.1s we generate a reset
// (this handles the reset button as well).
// Also generate a reset on start up (assuming FPGA regs start at 0).
//
module reset(clk, kbdata, rstn, expired, resetdone, rkbdata);

input  clk;              // system clock
input  kbdata;           // keyboard data line
output rstn;             // global out (active low)
output expired;
output resetdone;
output rkbdata;

reg rkbdata;             // registered kbdata

reg rstn;

parameter KBCNT = 22;
parameter POCNT = 25;	    // Way to large for simulations

// reg [KBCNT:0] count;        // counts low data on kbdata

reg [POCNT:0] porst;        // "power on" counter

initial begin    // Needed if simulating
//  count <= 0;
  porst <= 0;
end

wire expired;
wire resetdone;

assign expired = 0; // count[KBCNT];
assign resetdone = porst[POCNT];

always @ (posedge clk)
begin
  rkbdata <= kbdata;
end

//always @ (posedge clk)
//begin
//  if (rkbdata)
//    count <= 0;
//  else if (!expired)
//    count <= count + 1;
//end

always @ (posedge clk)
begin
  if (!rkbdata && expired)
    porst <= 0;
  else 
    if (!resetdone)
      porst <= porst+1;
end

always @ (posedge clk)
begin
  rstn <= resetdone;
end

endmodule
