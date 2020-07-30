
import StmtFSM::*;

import VendingIfc::*;
import Vending::*;

// Vending machine testbench
// Uses FSM library
(* synthesize *)
module sysTestVending(Empty);

  // Instantiate the dut
  Vending machine();
  mkVending the_machine(machine);

  // Constantly display the vending machine outputs
  rule display_output;
    if (machine.dispense_gum)
      $display("Dispensing gum at time %0t", $time);
    if (machine.dispense_ten_cents)
      $display("Dispensing ten cents at time %0t", $time);
  endrule

   // Execute the vending machine action
   // And display output in parallel  
   Stmt test_prog =
   (seq
       action 
         machine.ten_cent_in;
         $display ("Insert ten cents at time %0t", $time);
       endaction
       action 
         machine.ten_cent_in;
         $display ("Insert ten cents at time %0t", $time);
       endaction
       action
         machine.fifty_cent_in;
         $display ("Insert fifty cents at time %0t", $time);
       endaction
       action 
         machine.money_back_button;
         $display ("Press money back button at time %0t", $time);
       endaction
       action 
         machine.ten_cent_in;
         $display ("Insert ten cents at time %0t", $time);
       endaction
       action 
         machine.money_back_button;
         $display ("Press money back button at time %0t", $time);
       endaction       
       // Wait before finishing (for extra output)
       noAction;
       noAction;
       $display("Testbench finished at time %0t", $time);
    endseq);

    // Build an FSM for the test program
    FSM test_fsm <- mkFSM(test_prog); 

    Reg#(Bool) test_started <- mkReg(False);

    // Start the test program
    rule start_it (!test_started);
       test_started <= True;
       test_fsm.start();
    endrule

    // Exit simulation when the test_fsm is finished
    rule exit(test_started && test_fsm.done);
      $finish(0);
    endrule

endmodule
