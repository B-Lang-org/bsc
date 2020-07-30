import "BDPI" function UInt#(7) popcount (UInt#(97) x);

(* synthesize *)
module mkBDPIBit97 ();

   Reg#(UInt#(4)) count <- mkReg(0);
   Reg#(UInt#(97)) x <- mkReg(42);

   rule incr (count < 15);
       count <= count + 1;
   endrule: incr

   rule r;
      $display("popcount(%h) = %d", x, popcount(x));
      x <= (x << 4) + ~x;
   endrule: r

   rule done (count == 15);
      $finish(0);
   endrule: done

endmodule
