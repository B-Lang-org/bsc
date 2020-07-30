
module RRSPSRAM_65536_16_bussed (CLK,A,DI,ENABLE,WE,DO);

  parameter WIDTH = 16;
  parameter DEPTH = 65536;

  input              CLK;
  input [WIDTH-1 :0] A;
  input [WIDTH-1 :0] DI;
  input              ENABLE;
  input              WE;
  output [WIDTH-1 :0] DO;

  reg [WIDTH-1 :0] mem[DEPTH-1 :0];
  reg [WIDTH-1 :0] DO;

  always@(posedge CLK)
  begin
    if (ENABLE)
	  begin
	    if (WE)
		   mem[A] <= DI;
		else
		   DO <= mem[A];
	  end
  end

endmodule
