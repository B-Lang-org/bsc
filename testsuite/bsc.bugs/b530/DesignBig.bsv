package DesignBig;


interface DESIGN_IFC;
  
   method Bit#(11) out();
   method Bit#(11) out2();
   method Bit#(11) out3();
   method Bit#(11) out4();
endinterface: DESIGN_IFC




module mkDesign (DESIGN_IFC);

  method Bit#(11) out();
// if bounds checking is not done, this will segfault or otherwise
// fail by running out of memory.  This is a pretty evil testcase,
// likely to hose tinderbox if bounds checking gets broken.
  out = 1<< 4000000000;
  
  endmethod: out

  method Bit#(11) out2();
  Integer x = 4000000000;
  out2 = 1<< x;
  
  endmethod

  method Bit#(11) out3();
  // make the evaluator do some work.
  Integer x = 2000000000;
  Integer y = 2000000000;
  out3 = 1<< (x+y);
  
  endmethod

  method Bit#(11) out4();
  int x = 2000000000;
  out4 = 1<< x;
  
  endmethod

endmodule: mkDesign
                 
endpackage: DesignBig
