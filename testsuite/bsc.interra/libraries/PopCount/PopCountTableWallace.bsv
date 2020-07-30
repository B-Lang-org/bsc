package PopCountTableWallace;

import PopCount :: *;

interface Design_IFC;
   method Bit #(4) start(Bit #(8) x);
endinterface : Design_IFC

module mkDesign_PopCountTableWallace (Design_IFC);

   method Bit#(4) start (Bit#(8) x);
   
       return popCountTableWallace(x);
       
   endmethod : start
   
endmodule : mkDesign_PopCountTableWallace

module mkTestbench_PopCountTableWallace ();

   Reg #(Bit #(8)) counter();
   mkReg #(0) the_counter(counter);

   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);

   Design_IFC dut();
   mkDesign_PopCountTableWallace the_dut (dut);

   rule always_true (True);
       counter <= counter + 1;
       
       Bit #(4) expected = 0;
       
       for (Integer x = 0; x < 8; x = x + 1)
         expected = expected + zeroExtend(counter[x]);

       $display ("Counter = %b, PopCountTableWallace = %d", counter, dut.start(counter));
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
       
endmodule : mkTestbench_PopCountTableWallace   

endpackage : PopCountTableWallace
