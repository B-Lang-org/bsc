package Format2;


(* synthesize *)
module sysFormat2 (Empty);
   
   Reg#(Bit#(8)) count <- mkReg(0);
   
   rule every;
      let f = $format("(%0d) ", count);
      let g = $format("A ", f);
      $display("(%0d) XYZ ", count, g, " ", f);
      count <= count + 1;
      if (count == 10) $finish;
   endrule
      
endmodule

endpackage