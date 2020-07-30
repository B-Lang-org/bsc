package Design;


interface DESIGN_IFC;
  
   method Bit#(11) out();
endinterface: DESIGN_IFC




module mkDesign (DESIGN_IFC);

  method Bit#(11) out();
// if bounds checking is not done, this will segfault or otherwise
// fail by running out of memory.  This is a pretty evil testcase,
// likely to hose tinderbox if bounds checking gets broken.
  out = 1<< -1;
  
  endmethod: out

endmodule: mkDesign
                 
endpackage
