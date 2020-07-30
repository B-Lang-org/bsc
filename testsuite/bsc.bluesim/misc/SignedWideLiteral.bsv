Int#(43) a = 43'b0000000000000000000000011111111011101100000;
Int#(23) b = 23'b00101001110010111100000;

// This testcase revealed a bug where statements of the form
// "x = <constant>", where "x" is a wide def, were being generated
// as just "<constant>" because the expression was mistakenly
// determined to be a wide operation.  The multiplication was needed
// to trigger the right situation for the bug.

(* synthesize *)
module sysSignedWideLiteral();
   
   Int#(66) prod0 = signedMul(a,b);   

   rule test;
      $display("%h",prod0);
      $finish(0);
   endrule
   
endmodule
