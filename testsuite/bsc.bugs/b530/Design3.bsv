package Design3;


interface DESIGN_IFC;
  
   method Bit#(11) out3();
endinterface: DESIGN_IFC




module mkDesign (DESIGN_IFC);

  method Bit#(11) out3();
  // make the evaluator do some work.
  Integer x = -1;
  Integer y = -1;
  out3 = 1<< (x+y);
  
  endmethod


endmodule: mkDesign
                 
endpackage
