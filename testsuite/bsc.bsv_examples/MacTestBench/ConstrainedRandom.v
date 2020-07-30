////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

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
        if (!RST)
          OUT <= min;
        else if (EN)
	  begin
	     i = 0;
	     OUT2 = 0;
	     for (i = 0; i <= width; i = i + 32) begin
		OUT2 = {OUT2, $random};
	     end
	     if ((1 + (max - min)) == 0)
	       OUT <= min + OUT2;
	     else
	       OUT <= min + (OUT2 % (1 + (max - min)));
	  end
	
     end

   // synopsys translate_off
   initial begin
      OUT = {((128 + 1)/2){2'b10}} ;
   end
   // synopsys translate_on


endmodule // ConstrainedRandom

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

