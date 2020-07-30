import FIFO :: *;

(*noinline*)
function Bool returnBool(Bool b); return b; endfunction

(* synthesize *)
module mkBug1741_Not();

   Reg#(Bool) c <- mkReg(True);

   FIFO#(Bool) f <- mkFIFO;

   (* conflict_free = "r1, r2" *)
   rule r1;
      let b1 = returnBool(True);
      if (c)
         if (!b1)
            f.enq(True);
   endrule

   rule r2 (!c);
      f.enq(False);
   endrule

endmodule
