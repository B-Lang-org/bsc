package Design4;


interface DESIGN_IFC;
  
   method Bit#(11) out4();
endinterface: DESIGN_IFC




module mkDesign (DESIGN_IFC);

  method Bit#(11) out4();
  int x = -1;
  out4 = 1<< x;
  
  endmethod

endmodule: mkDesign
                 
endpackage
