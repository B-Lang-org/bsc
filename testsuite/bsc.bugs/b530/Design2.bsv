package Design2;


interface DESIGN_IFC;
  
   method Bit#(11) out2();
endinterface: DESIGN_IFC




module mkDesign (DESIGN_IFC);

  method Bit#(11) out2();
  Integer x = -1;
  out2 = 1<< x;
  
  endmethod


endmodule: mkDesign
                 
endpackage
