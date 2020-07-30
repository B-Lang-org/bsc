interface IFC;
   method Action start(Bit#(1) x1, Bit#(2) x2, Bit#(3) x3, Bit#(4) x4,
		       Bit#(5) x5, Bit#(6) x6, Bit#(7) x7, Bit#(8) x8);
endinterface

module mkSub (IFC);
   method Action start(x1, x2, x3, x4, x5, x6, x7, x8);
      $display(x1, x2, x3, x4, x5, x6, x7, x8);
   endmethod
endmodule

module mkTop (IFC);

   IFC sub <- mkSub;

   //Error is not pointing to x5 is missing or 5th argument is mismatch
   method Action start(x1, x2, x3, x4, x5, x6, x7, x8);
      sub.start(x1, x2, x3, x4, x6, x7, x8);
   endmethod

endmodule
