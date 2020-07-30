module Both(CLK, INOUT);
   parameter outvalue=99;
   parameter setpt=0;
   parameter readpt=0;
   parameter loopat=3;
   
   input CLK;
   //input EN;
   inout [31:0] INOUT;

   reg [31:0]  hold;
   wire [31:0] hold$D_IN;
   assign      INOUT=hold;

   reg [31:0]  count=0;
   wire [31:0] count$D_IN;

   always @(negedge CLK)
     begin
        if (count==readpt)
          $display("Sender",outvalue, "(",count,")  ",INOUT);
     end
   
   assign      hold$D_IN = (count == setpt)? outvalue : (32'bz);
   assign      count$D_IN = (count != loopat) ? (count + 1) : 32'd0 ;
   
   always @(posedge CLK)
     begin
        count <= count$D_IN;
        hold <= hold$D_IN;
     end

   
     
endmodule // Both
