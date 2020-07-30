(* synthesize *)
module sysWideModArgPortTest();
  let x <- mkWideModArgPortTest_Sub(12, 5);
endmodule

// The test for Bug 1611 requires the non-parameter argument.
// The parameter argument and the interface are there to test
// for C++ warnings if initializations of the members happen in
// the wrong order (and the plus operation in the module is to
// create wide local defs for this purpose too).

(* synthesize *)
module mkWideModArgPortTest_Sub
          #(parameter Bit#(65) val1, Bit#(65) val2)
          (Reg#(Bit#(65)));

   Reg#(Bool) started <- mkReg(False);
   Reg#(Bit#(65)) sum <- mkReg(val1);
   Reg#(Bit#(65)) cnt <- mkRegU;

   rule start (!started);
      cnt <= val1 + val2;
      started <= True;
   endrule

   rule count (started && (cnt > 0));
      $display("Count: %x", cnt);
      cnt <= cnt - 1;
   endrule

   rule finish (started && (cnt == 0));
      $finish(0);
   endrule

   return sum;
endmodule

