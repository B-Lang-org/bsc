package Reserved_test;

import Reserved :: *;

module mkTestbench_Reserved_test();

 //Conversion From Bits
   Reserved #(8) reserve1 = unpack (5);
   Reserved #(8) reserve2 = unpack (6);
 
 //Conversion to Bits
   Bit #(8) toBits1 = pack (reserve1);
   Bit #(8) toBits2 = pack (reserve2);
   
 //Checking for boundedness
   Reserved #(8) maximum_bound = maxBound;
   Reserved #(8) minimum_bound = minBound;
   
   
 //Checking for Eq and Ord derivativeness
   rule always_fire (True);
      if (reserve1 < reserve2 || reserve1 > reserve2 || reserve1 != reserve2 || minimum_bound < maximum_bound || minimum_bound > maximum_bound || minimum_bound != maximum_bound)
        $display ("Simulation Fails");
      else if (reserve1 == reserve2 && minimum_bound == maximum_bound)
        $display ("Simulation Passes");
      $finish(2'b00);
   endrule
endmodule : mkTestbench_Reserved_test

endpackage : Reserved_test
