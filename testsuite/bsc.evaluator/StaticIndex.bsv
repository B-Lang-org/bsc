// simple test of toStaticIndex for all index types
Integer testInteger = -9999;
Bit#(32) testBit = 'hDEADBEEF;
Int#(8) testInt = 'h6c;
UInt#(9) testUInt = 99;

(* synthesize *)
module sysStaticIndex();
   rule test;
      $display("Integer: %0d", toStaticIndex(testInteger));
      $display("Bit: %h", toStaticIndex(testBit)); 
      $display("Int: %h", toStaticIndex(testInt));
      $display("UInt: %0d", toStaticIndex(testUInt));
      $finish(0);
   endrule
endmodule
