package EqTest;

import EqFunction :: *;

function Bit #(8) sum_n (Bit #(4) n);
   if (n[0:0] == 0) 
      return (zeroExtend ({1'b0, n[3:1]}) * zeroExtend (n+1));
   else
      if (n==15) 
         return 8'd120;
      else
         return (zeroExtend ({1'b0, (n+1)[3:1]}) * zeroExtend (n));
endfunction : sum_n

function Bit #(8) sum_n_recursive (Bit #(4) n);
   if (n == 0)
      return zeroExtend (n);
   else 
      return (zeroExtend (n) + sum_n_recursive (n-1));
endfunction : sum_n_recursive

module mkTestbench_EqTest ();
   rule always_true (True);
          if (sum_n == sum_n_recursive)
            $display("Simulation Passes");
          else
            $display("Simulation Fails");
          $finish(2'b00);
   endrule
endmodule : mkTestbench_EqTest

endpackage : EqTest
   
