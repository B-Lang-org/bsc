(* synthesize *)
module bsvDisplayString#(parameter String s)(Empty ifc);
   
   rule test;
      $display("string %s", s);
      $finish(0);
   endrule

endmodule


(* synthesize *)
module mkStringPassThrough#(parameter String s)();
   bsvDisplayString(s);
endmodule

(* synthesize *)
module sysTwoLevelString();
   mkStringPassThrough("Test string");
endmodule
