package Testbench;
import Design :: *;

function Bit #(1) parity (Bit #(8) x);
  parity = x[7] ^ x[6] ^ x[5] ^ x[4] ^ x[3] ^ x[2] ^ x[1] ^ x[0];
endfunction:parity

module mkTestbench (Empty);
   Reg #(Bit #(32)) counter <- mkReg (0);
   Reg #(Bit #(32)) passes <- mkReg (0);
   Reg #(Bit #(32)) fails <- mkReg (0);
   Design_IFC dut <- mkDesign;
      
   Bit #(1) expected_parity = parity (counter [7:0]);

   rule processing (counter <= 32'hFF);
       action
          counter <= counter + 1;
          $display ("Input= %d, Parity = %d, Expected = %d", counter, dut.parity (counter[7:0]), expected_parity);
          if ((dut.parity(counter[7:0]) == expected_parity))
             passes <= passes + 1;
          else
             fails <= fails + 1;
       endaction
   endrule

   
   rule result (counter == 32'h100);
       action
          $display ("Pass %d, Fails %d", passes, fails);
          counter <= counter + 1;
       endaction
   endrule
     
        
endmodule : mkTestbench

endpackage : Testbench
