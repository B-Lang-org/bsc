module RPC(ARG, ARGW, RESULT, RESW, SETR);
   parameter widtha = 1;
   parameter widthr = 1;
            
// input                    CLK;
   input [widtha - 1 : 0]   ARG;
   output[widtha - 1 : 0]   ARGW;
   input [widthr - 1 : 0]   RESW;
   output[widthr - 1 : 0]   RESULT;
   input                    SETR;
   
   assign ARGW = ARG;
   assign RESULT = RESW;

endmodule
