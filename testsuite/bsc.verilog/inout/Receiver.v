module Receiver(CLK, IN);
   
   input CLK;
   inout [31:0] IN;

   always @(negedge CLK)
     begin
        $display(IN);
     end
endmodule // Receiver
