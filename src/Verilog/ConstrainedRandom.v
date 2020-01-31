
`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif


module ConstrainedRandom(CLK, RST, OUT, EN);

   parameter width = 1 ;
   parameter min = 0 ;
   parameter max = 0 ;

   input           CLK;
   input           RST;
   input           EN;
   output [width - 1: 0] OUT;

   reg [width - 1: 0]    OUT;
   reg [width - 1: 0]    OUT2;

   integer 	    i;
   always@(posedge CLK)
     begin
        if (RST == `BSV_RESET_VALUE)
          OUT <= min;
        else if (EN)
	  begin
	     i = 0;
	     OUT2 = 0;
	     for (i = 0; i <= width; i = i + 32) begin
		OUT2 = {OUT2, $random};
	     end
	     if ((1 + (max - min)) == 0)
	       OUT <= `BSV_ASSIGNMENT_DELAY min + OUT2;
	     else
	       OUT <= `BSV_ASSIGNMENT_DELAY min + (OUT2 % (1 + (max - min)));
	  end

     end

   // synopsys translate_off
   initial begin
      OUT = {((width + 1)/2){2'b10}} ;
   end
   // synopsys translate_on


endmodule // ConstrainedRandom


