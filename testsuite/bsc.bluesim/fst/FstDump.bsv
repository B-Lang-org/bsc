// Tests for Bluesim FST waveform dumping (-dump-formats fst).
// One shared synthesized core, instantiated by a separate top module
// for each -dump-formats configuration so that each configuration
// links to its own executable.

(* synthesize *)
module mkFstDumpCore();
   Reg#(UInt#(8)) counter <- mkReg(0);
   Reg#(Bit#(48)) mid <- mkReg(0);
   Reg#(Bit#(128)) wide <- mkReg(0);

   rule count;
      counter <= counter + 1;
      mid <= mid + 7;
      wide <= wide + 3;
   endrule

   rule show (counter % 10 == 5);
      $display("counter = %0d mid = %0d wide = %0d", counter, mid, wide);
   endrule

   rule done (counter == 42);
      $finish(0);
   endrule
endmodule

(* synthesize *)
module sysFstDump();
   Empty core <- mkFstDumpCore;
endmodule

(* synthesize *)
module sysFstBoth();
   Empty core <- mkFstDumpCore;
endmodule

(* synthesize *)
module sysFstVcdOnly();
   Empty core <- mkFstDumpCore;
endmodule

(* synthesize *)
module sysFstNone();
   Empty core <- mkFstDumpCore;
endmodule
