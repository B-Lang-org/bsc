// test a mutually exclusive check failing at runtime

(* synthesize *)
module sysMutuallyExclusiveCheck(Empty);

   Reg#(Bit#(64)) r <- mkReg(0);
   
   Reg#(Bool) done <- mkReg(False);

   rule watch;
     done <= !done;
// if r printed Verilog and Bluesim would have different results
//   $display("r is %0d", r);
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

