(* synthesize *)
module sysPrimUndefined();
  rule test;
     Bit#(83) u = ?;
     $display("Undefined: %h", u);
     $finish(0);
  endrule
endmodule
      
