module RegisteredSender(CLK, EN, SETVAL, OUT);
   
   input CLK;
   input EN;
   input [31:0] SETVAL;
   
   inout [31:0] OUT;

   reg [31:0]  hold;

   assign OUT=hold;

   always @(posedge CLK) begin
      if (EN)
        hold <= SETVAL;
   end
   
endmodule // Sender
