package Format4;


(* synthesize *)
module sysFormat4 (Empty);
   
   Reg#(Bit#(8)) count <- mkReg(0);
   
   rule every;
      let f = $format("(%0d) ", count);
      let g = $format("A ", f);
      Bit#(640) h <- $swriteAV("(%0d) XYZ ", $time, g, " ", f);
      $display("AA  %s BB", h);
      count <= count + 1;
      if (count == 10) $finish;
   endrule
      
endmodule

endpackage