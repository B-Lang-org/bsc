import "BDPI" function Int#(n) poly_add (Int#(n) x, Int#(n) y, UInt#(32) size);

function Int#(n) my_add(Int#(n) x, Int#(n) y);
  return poly_add(x, y, fromInteger(valueOf(n)));
endfunction: my_add

(* synthesize *)
module mkBDPIBitN ();
   rule r;
      Int#(7) x7 = 1;
      Int#(7) y7 = 2;
      $display("  7-bit add: %d", my_add(x7,y7));

      Int#(8) x8 = 1;
      Int#(8) y8 = 2;
      $display("  8-bit add: %d", my_add(x8,y8));

      Int#(17) x17 = 1;
      Int#(17) y17 = 2;
      $display(" 17-bit add: %d", my_add(x17,y17));

      Int#(31) x31 = 1;
      Int#(31) y31 = 2;
      $display(" 31-bit add: %d", my_add(x31,y31));

      Int#(32) x32 = 1;
      Int#(32) y32 = 2;
      $display(" 32-bit add: %d", my_add(x32,y32));

      Int#(33) x33 = 1;
      Int#(33) y33 = 2;
      $display(" 33-bit add: %d", my_add(x33,y33));

      Int#(63) x63 = 1;
      Int#(63) y63 = 2;
      $display(" 63-bit add: %d", my_add(x63,y63));

      Int#(64) x64 = 1;
      Int#(64) y64 = 2;
      $display(" 64-bit add: %d", my_add(x64,y64));

      Int#(65) x65 = 1;
      Int#(65) y65 = 2;
      $display(" 65-bit add: %d", my_add(x65,y65));

      Int#(128) x128 = 1;
      Int#(128) y128 = 2;
      $display("128-bit add: %d", my_add(x128,y128));

      // 263 is a prime :)
      Int#(263) x263 = 1;
      Int#(263) y263 = 2;
      $display("263-bit add: %d", my_add(x263,y263));

      $finish(0);
   endrule
endmodule

