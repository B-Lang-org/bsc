
module InoutConnect(
                    .X1(internal), 
                    .X2(internal)
                    );


   parameter width = 1;
   
   inout [ width - 1 : 0 ] internal;
endmodule // InoutConnect
