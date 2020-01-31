
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


module CRegN5
         (CLK,
          RST,

	  // port 0 read
          Q_OUT_0,
	  // port 0 write
          EN_0, D_IN_0,

          // port 1 read
          Q_OUT_1,
	  // port 1 write
          EN_1, D_IN_1,

          // port 2 read
          Q_OUT_2,
	  // port 2 write
          EN_2, D_IN_2,

          // port 3 read
          Q_OUT_3,
	  // port 3 write
          EN_3, D_IN_3,

          // port 4 read
          Q_OUT_4,
	  // port 4 write
          EN_4, D_IN_4
         );

   parameter width = 1 ;
   parameter init  = { width {1'b0} } ;

   input  CLK ;
   input  RST ;

   output [width - 1 : 0]  Q_OUT_0 ;
   input                   EN_0 ;
   input  [width - 1 : 0]  D_IN_0 ;

   output [width - 1 : 0]  Q_OUT_1 ;
   input                   EN_1 ;
   input  [width - 1 : 0]  D_IN_1 ;

   output [width - 1 : 0]  Q_OUT_2 ;
   input                   EN_2 ;
   input  [width - 1 : 0]  D_IN_2 ;

   output [width - 1 : 0]  Q_OUT_3 ;
   input                   EN_3 ;
   input  [width - 1 : 0]  D_IN_3 ;

   output [width - 1 : 0]  Q_OUT_4 ;
   input                   EN_4 ;
   input  [width - 1 : 0]  D_IN_4 ;

   reg    [width - 1 : 0]  Q_OUT_0 ;
   wire   [width - 1 : 0]  Q_OUT_1 ;
   wire   [width - 1 : 0]  Q_OUT_2 ;
   wire   [width - 1 : 0]  Q_OUT_3 ;
   wire   [width - 1 : 0]  Q_OUT_4 ;
   wire   [width - 1 : 0]  Q_OUT_5 ;
   
   assign Q_OUT_1 = EN_0 ? D_IN_0 : Q_OUT_0 ;
   assign Q_OUT_2 = EN_1 ? D_IN_1 : Q_OUT_1 ;
   assign Q_OUT_3 = EN_2 ? D_IN_2 : Q_OUT_2 ;
   assign Q_OUT_4 = EN_3 ? D_IN_3 : Q_OUT_3 ;
   assign Q_OUT_5 = EN_4 ? D_IN_4 : Q_OUT_4 ;
   
   always@(posedge CLK)
     begin
        if (RST == `BSV_RESET_VALUE)
          Q_OUT_0 <= `BSV_ASSIGNMENT_DELAY init ;
        else
          Q_OUT_0 <= `BSV_ASSIGNMENT_DELAY Q_OUT_5 ;
     end

`ifdef BSV_NO_INITIAL_BLOCKS
`else // not BSV_NO_INITIAL_BLOCKS
   // synopsys translate_off
   initial begin
      Q_OUT_0 = {((width + 1)/2){2'b10}} ;
   end
   // synopsys translate_on
`endif // BSV_NO_INITIAL_BLOCKS

endmodule

