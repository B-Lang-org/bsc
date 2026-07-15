// The $dump* system tasks are format-agnostic: on a model built with
// -dump-formats fst they dump FST into the $dumpfile-named file
// (like iverilog, where "vvp -fst" chooses the on-disk encoding).

(* synthesize *)
module sysFstTasks();
   Reg#(UInt#(8)) t <- mkReg(0);
   Reg#(Bit#(16)) v <- mkReg(0);

   rule tick;
      t <= t + 1;
      v <= v + 5;
   endrule

   rule start (t == 2);
      $dumpfile("sysFstTasks.fst");
      $dumpvars;
   endrule

   rule stop (t == 10);
      $dumpoff;
   endrule

   rule chk (t == 15);
      $dumpall;
   endrule

   rule restart (t == 20);
      $dumpon;
      $display("dumping restarted at %0d", t);
   endrule

   rule fin (t == 30);
      $display("final v = %0d", v);
      $finish(0);
   endrule
endmodule
