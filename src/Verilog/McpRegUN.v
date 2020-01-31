
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



module McpRegUN(CLK, RST, SET, val, get);
   parameter width = 1;
   parameter delay = 0;

   input     CLK;
   input     RST;
   input     SET;
   input [width - 1 : 0] val;
   output [width - 1 : 0] get;

   reg [width - 1 : 0]    get;

`ifdef DC
`else
   wire [width - 1 : 0]   #delay delayed_val = val;
   wire [width - 1 : 0]   output_val = (val === delayed_val ? val : {width{1'bx}});
`endif

   always@(posedge CLK /* or `BSV_RESET_EDGE RST */)
     begin
        if (RST == `BSV_RESET_VALUE)
          begin
             get <= `BSV_ASSIGNMENT_DELAY {((width + 1)/2){2'b10}} ;
          end
        else begin
           if (SET)
             begin
`ifdef DC
                get <= `BSV_ASSIGNMENT_DELAY val;
`else
                get <= `BSV_ASSIGNMENT_DELAY output_val;
`endif
             end // if (SET)
        end // else: !if(RST == `BSV_RESET_VALUE)
     end // always@ (posedge CLK or `BSV_RESET_EDGE RST)


`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      get = {((width + 1)/2){2'b10}} ;
   end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule

