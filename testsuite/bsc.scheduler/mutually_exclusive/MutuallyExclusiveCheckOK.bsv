// test a mutually exclusive check failing at runtime

(* synthesize *)
module sysMutuallyExclusiveCheckOK(Empty);

   Reg#(Bit#(64)) r <- mkReg(1);
   
   Reg#(Bool) done <- mkReg(False);

   rule watch;
     done <= !done;
     $display("r is %0d", r);
     if(done) $finish(0);
   endrule
   
   rule zero(r == 0);
      r <= 1;
   endrule
   
   (* mutually_exclusive = "zero, two" *)
   rule two(r < 2);
      r <= 2;
   endrule

   rule three(r == 3);
      r <= 4;
   endrule
   
endmodule

