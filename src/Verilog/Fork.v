
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module Fork(i, o);

   parameter iw = 1;
   parameter ow = 2;

   input [iw - 1 : 0] i;
   
   output [ow - 1 : 0] o;

   assign 		      o = { i, i };
   
endmodule

