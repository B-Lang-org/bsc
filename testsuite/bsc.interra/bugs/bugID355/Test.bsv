interface DESIGN_IFC_SBOX1;
   method Bit#(4) dout(Bit#(7) addr);
endinterface: DESIGN_IFC_SBOX1

module sbox1 (DESIGN_IFC_SBOX1);

  method Bit#(4) dout(Bit#(7) addr);
     case (addr[5])
         0:  dout =  14;
     endcase
  endmethod: dout

endmodule: sbox1
