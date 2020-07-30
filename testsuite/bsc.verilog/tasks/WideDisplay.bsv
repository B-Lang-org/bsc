package WideDisplay;

(* synthesize *)
module sysWideDisplay (Empty);
   
   Reg#(Bit#(256)) count <- mkReg(0);
   
   rule every;
      count <= count + 1;
      $display("Value in decimal: %0d", count);
      $display("Value in hex:     %0h", count);
      $display("Value octal:      %0o", count);
      $display("Value in binary:  %0b", count);
      if (count == 10) $finish(0);
   endrule
      
endmodule

endpackage