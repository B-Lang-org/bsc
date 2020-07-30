// testbench for Mult1
import Design::*;

(* synthesize *)
module mkTestbench (Empty);

// Tin typedefed in design
   Reg#(Tin) x    <- mkReg(1);
   Reg#(Tin) y    <- mkReg(0);

// instantiating design   
   Mult_IFC dut <- mkDesign;
   
// Give 20 mplrs and multiplicands and verify result
   rule rule_tb_1 (x < 20);
      $display ($time,"    x = %d, y = %d", x, y);
      dut.start (x, y); // set data in start method
      x <= x + 1; // update value of x and y
      y <= y + 1;
   endrule

// Acknowledge receipt of data
   rule rule_tb_2 (x < 20);
      let z = dut.result(); // call result method
      $display($time,"    Result = %d", z); // display result
   endrule
   
// Rule to invoke $finish(0) after 20 cycles
   rule stop (x == 20);
      $finish(0);
   endrule
endmodule
