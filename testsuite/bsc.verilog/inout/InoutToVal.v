module InoutToVal(IN,OUT,CLK);

   input CLK;
   inout [31:0] IN;
   output [31:0] OUT;
   reg [31:0] 	 OUT;

   always @(posedge CLK) begin
      OUT <= IN;
   end

endmodule // InoutToVal
