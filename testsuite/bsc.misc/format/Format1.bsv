package Format1;


(* synthesize *)
module sysFormat1 (Empty);
   
   Reg#(Bit#(8)) count <- mkReg(0);
   
   rule every;
      Fmt f = $format("(%0d)", count + 1);
      $display(" XYZ ", f, " ", $format("(%0d) ", count));
      count <= count + 1;
      if (count == 10) $finish;
   endrule
      
endmodule

endpackage