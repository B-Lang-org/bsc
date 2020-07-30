import Memory::*;

(* synthesize *)
module sysParseTest();

Memory mem <- mkMemory();

rule r;
  $display("%h", mem.read_mem(0));
  $finish(0);
endrule: r

endmodule: sysParseTest
