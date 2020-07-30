(* synthesize *)
module sysPreempts();

   Reg#(Bool) c1 <- mkRegU;
   Reg#(Bool) c2 <- mkRegU;
   Reg#(Bool) c3 <- mkRegU;
   Reg#(Bool) c4 <- mkRegU;

   (* preempts="r0, (r1,r2,r3)" *)
   rule r0 (c1 || c2 || c3);
      $display("r0");
   endrule

   // Will never fire
   rule r1 (c1 || c2);
      $display("r1");
   endrule

   // Will never fire
   rule r2 (c3 && c4);
      $display("r2");
   endrule

   // Can still fire in some cases
   rule r3 (c3 || c4);
      $display("r3");
   endrule

endmodule

