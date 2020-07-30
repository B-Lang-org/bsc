package MkListReg;

import List :: *;
import Vector :: *;
import ListReg :: *;

function UInt #(8) f (UInt #(8) a, UInt #(8) b);
    return (a+b);
endfunction

interface Design_IFC;
    method Action add_entries (UInt #(8) a);
    method UInt #(8) sum ();
    
endinterface

module mkDesign_MkListReg (Design_IFC);
    Reg #(List #(UInt #(8))) my_list();
    mkListReg #(List :: replicate (10, 0)) the_my_list(my_list);
    
    method add_entries (a);
     action
        my_list <= Cons (a, List :: init(my_list));
     endaction
    endmethod: add_entries

    method sum ();
        sum = List :: foldl (f, 0, my_list);
    endmethod: sum

endmodule : mkDesign_MkListReg

module mkTestbench_MkListReg();
   Design_IFC dut();
   mkDesign_MkListReg the_dut (dut);

   Reg #(UInt #(8)) counter();
   mkReg #(0) the_counter (counter);
   
   Reg #(UInt #(8)) test_counter();
   mkReg #(0) the_test_counter (test_counter);
   
   
   
   rule always_true(True);
       counter <= counter + 1;
   endrule
  

   rule add_to_list (counter<10);
       test_counter <= test_counter + counter;
       dut.add_entries (counter);
       if (dut.sum != test_counter)
           begin
              $display("Simulation Fails");
              $finish(2'b00);
           end
   endrule

        

   rule endsim (counter == 10);
       $display("Sum of Numbers 0 to 9 = %d",dut.sum); 
       if (dut.sum !=45)
           $display("Simulation Fails");
       else
           $display ("Simulation Passes");
       $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_MkListReg
endpackage : MkListReg
