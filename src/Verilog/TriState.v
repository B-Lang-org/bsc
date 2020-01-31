
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module TriState
  (
   // Outputs
   O, 
   // Inouts
   IO, 
   // Inputs
   OE, I
   );

   parameter          width = 1;
   
   
   input              OE;
   
   input [width-1:0]  I;
   output [width-1:0] O;

   inout [width-1:0]  IO;

   assign             IO = (OE) ? I : { width { 1'bz } };
   assign             O  = IO;
      
endmodule // TriState

