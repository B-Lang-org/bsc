interface DESIGN_IFC_SBOX1;
   method Bit#(4) dout(Bit#(7) addr);
endinterface: DESIGN_IFC_SBOX1

module sbox1 (DESIGN_IFC_SBOX1);

  method Bit#(4) dout(Bit#(7) addr);
     case ({addr[5], addr[0], addr[4:1]})
         0:  dout =  14;
         1:  dout =   4;
         2:  dout =  13;
         3:  dout =   1;
         default: dout = 0;
     endcase
  endmethod: dout

endmodule: sbox1
