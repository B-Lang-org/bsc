module EnabledReceiver(CLK, IN, EN);
   
   input CLK;
   input EN;
   
   inout [31:0] IN;

   always @(negedge CLK)
     begin
        if (EN)
          $display(IN);
     end
endmodule // Receiver
