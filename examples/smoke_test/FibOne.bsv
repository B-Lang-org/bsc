(* synthesize *)
module mkFibOne();
   // register containing the current Fibonacci value
   Reg#(int) this_fib();              // interface instantiation
   mkReg#(0) this_fib_inst(this_fib); // module instantiation
   // register containing the next Fibonacci value
   Reg#(int) next_fib();
   mkReg#(1) next_fib_inst(next_fib);

   rule fib;  // predicate condition always true, so omitted
      this_fib <= next_fib;
      next_fib <= this_fib + next_fib;  // note that this uses stale this_fib
      $display("%0d", this_fib);
      if ( this_fib > 10000 ) $finish(0) ;
  endrule: fib
endmodule: mkFibOne
