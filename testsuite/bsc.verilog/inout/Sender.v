module Sender(OUT);
   parameter outvalue=0;
   
   //input CLK;
   //input EN;
   inout [31:0] OUT;

   //reg   hold;

   assign OUT=outvalue;
endmodule // Sender
