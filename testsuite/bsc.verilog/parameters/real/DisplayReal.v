module DisplayReal(CLK);

   parameter val = 0.0;
   
   input CLK;

   always @(negedge CLK)
     begin
        $display("real number: %2.2f", val);
	$finish(0);
     end
endmodule // Receiver
