package PopCountNaive;

import PopCount :: *;

interface Design_IFC;
   method Bit #(4) start(Bit #(8) x);
endinterface : Design_IFC

module mkDesign_PopCountNaive (Design_IFC);
   method start (x);
       return popCountNaive(x);
   endmethod : start
endmodule : mkDesign_PopCountNaive

module mkTestbench_PopCountNaive ();
   Reg #(Bit #(8)) counter();
   mkReg #(0) the_counter(counter);

   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);

   Design_IFC dut();
   mkDesign_PopCountNaive the_dut (dut);

   rule always_true (True);
       counter <= counter + 1;
       Bit #(4) expected = zeroExtend (counter [7:7]) + zeroExtend (counter [6:6]) + zeroExtend (counter [5:5]) + zeroExtend (counter [4:4]) + zeroExtend (counter [3:3]) + zeroExtend (counter [2:2]) + zeroExtend (counter [1:1]) + zeroExtend (counter [0:0]);
       $display ("Counter = %b, PopCountNaive = %d", counter, dut.start(counter));
       if (dut.start(counter) != expected)
          fail <= True;
   endrule

   rule endsim (counter == 8'b11111111);
       if (!fail)
           $display ("Simulation Passes");
       else 
           $display ("Simulation Fails");

       $finish (2'b00);
   endrule
       
endmodule : mkTestbench_PopCountNaive   

endpackage : PopCountNaive
