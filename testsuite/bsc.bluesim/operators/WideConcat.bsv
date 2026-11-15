import Vector::*;

interface WideConcatSource;
   method Action advance;
   method Bit#(8255) value;
endinterface

// Keep a wide concatenation in a method return as well as in rule bodies.
(* synthesize *)
module mkWideConcatSource(WideConcatSource);
   Vector#(127, Reg#(Bit#(65))) sources;
   for (Integer i = 0; i < 127; i = i + 1)
      sources[i] <- mkReg(fromInteger(2**64 + i * 17));

   method Action advance;
      for (Integer i = 0; i < 127; i = i + 1)
         sources[i] <= sources[i] + 65'h100000001;
   endmethod

   method value = pack(readVReg(sources));
endmodule

(* synthesize *)
module sysWideConcat();
   Vector#(127, Reg#(Bit#(65))) sources;
   for (Integer i = 0; i < 127; i = i + 1)
      sources[i] <- mkReg(fromInteger(2**64 + i * 17));
   WideConcatSource wideSource <- mkWideConcatSource;

   // Exercise aligned and unaligned segments, segments wider than 64 bits,
   // and partial words at the top of the concatenated value.
   Reg#(Bit#(889)) packed7 <- mkReg(0);
   Reg#(Bit#(4064)) packed32 <- mkReg(0);
   Reg#(Bit#(8255)) packed65 <- mkReg(0);
   Reg#(Bit#(8)) cycle <- mkReg(0);
   Reg#(Bool) previousMatch <- mkReg(True);

   rule test;
      // Scan the stored segments against a scalar reference rather than
      // constructing the expected value with another large concatenation.
      // Cycle 2 checks segment 0; cycle 128 checks segment 126.
      Bit#(8) index = cycle - 2;
      Bit#(16) shiftIndex = zeroExtend(index);
      Bit#(7) observed7 = truncate(packed7 >> (shiftIndex * 7));
      Bit#(32) observed32 = truncate(packed32 >> (shiftIndex * 32));
      Bit#(65) observed65 = truncate(packed65 >> (shiftIndex * 65));
      Bit#(65) expected = 65'h10000000100000001 + zeroExtend(index) * 17;
      Bool valuesMatch = observed7 == truncate(expected) &&
                         observed32 == truncate(expected) &&
                         observed65 == expected;
      // Register the comparison so scheduling system tasks does not require
      // reasoning about the entire wide value.
      previousMatch <= valuesMatch;
      if (cycle > 2 && !previousMatch) begin
         $display("FAIL: wide concatenation at cycle %0d", cycle - 1);
         $finish(1);
      end
      else if (cycle == 129) begin
         $display("PASS");
         $finish(0);
      end

      // Capture once, then keep advancing the sources while the guard is
      // false. Every part of the captured value must remain untouched.
      if (cycle == 1) begin
         Vector#(127, Bit#(65)) values = readVReg(sources);
         Vector#(127, Bit#(7)) values7 = map(truncate, values);
         Vector#(127, Bit#(32)) values32 = map(truncate, values);
         packed7 <= pack(values7);
         packed32 <= pack(values32);
         packed65 <= wideSource.value;
      end

      for (Integer i = 0; i < 127; i = i + 1)
         sources[i] <= sources[i] + 65'h100000001;
      wideSource.advance;
      cycle <= cycle + 1;
   endrule
endmodule
