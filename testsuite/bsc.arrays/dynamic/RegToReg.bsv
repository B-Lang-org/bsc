import Vector :: *;

(* synthesize *)
module sysRegToReg();
   Reg#(Vector#(8, UInt#(8))) rg <- mkReg(replicate(0));

   Reg#(UInt#(3)) idx <- mkReg(0);
   Reg#(Bool) done <- mkReg(False);

   rule do_upd (!done);
      let v = rg;
      v[idx] = zeroExtend(idx) + 1;
      rg <= v;
      if (idx == 7)
         done <= True;
   endrule

   rule do_done (done);
      $finish(0);
   endrule
endmodule

