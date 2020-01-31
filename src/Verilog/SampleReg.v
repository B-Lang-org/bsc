
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module SampleReg(CLK, D_IN, SCAN_IN, SCAN_OUT, SCAN_MODE, SCAN_ANY) ;
   parameter width = 1;
   parameter SCAN_WIDTH = 1;

   input                        CLK;
   input  [width - 1 : 0]       D_IN;
   input  [(SCAN_WIDTH - 1):0] SCAN_IN ; 
   output [(SCAN_WIDTH - 1):0] SCAN_OUT ; 
   input 			SCAN_MODE ; 
   input 			SCAN_ANY ; 
   reg [width - 1 : 0] 	        Q;
   reg [(SCAN_WIDTH - 1):0] 	_SCAN ; 

   always @(posedge CLK)
     begin
        {_SCAN,Q} <=  `BSV_ASSIGNMENT_DELAY (!SCAN_ANY) ? {_SCAN, D_IN} : ((SCAN_MODE) ? {Q,SCAN_IN} :  {_SCAN,Q});
     end // always @(posedge CLK)
   assign SCAN_OUT = _SCAN ; 
   
endmodule
