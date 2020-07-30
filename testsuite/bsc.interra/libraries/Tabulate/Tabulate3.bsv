package Tabulate3;

import Tabulate :: *;

function Bit #(5) fact (Bit #(5) a) ;
   Bit #(5) temp;
   if (a<=1) 
     temp = 1;
   else
     temp = a * fact (a-1);
   return temp;
endfunction: fact

function  (Bit #(5)) tabulated_fact (Bit #(5) a);
    return ((tabulate (fact)) (a)) ;
endfunction: tabulated_fact


interface IFC;
   method Bit #(5) start (Bit #(5) a);
endinterface : IFC

module mkDesign_Tabulate3 (IFC);
  method start (a);
     return (tabulated_fact (a));
  endmethod : start
endmodule : mkDesign_Tabulate3


module mkTestbench_Tabulate3 ();

   IFC dut();
   mkDesign_Tabulate3 the_dut (dut);

   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);
   
   Reg #(Bit #(5)) counter();
   mkReg #(0) the_counter(counter);

   rule always_true (True);
      counter <= counter + 1;
      $display ("Num=%d, Fact=%d", counter, dut.start(counter) );
      if (dut.start(0) != fact(0) || dut.start(1) !=fact(1) || dut.start (2) != fact(2) || dut.start (3) != fact(3) || dut.start (4) != fact(4) )
        fail <= True;
   endrule

   rule result (counter == 5);
      if (fail) 
         $display ("Simulation Fails");
      else
         $display ("Simulation Passes");
      $finish (2'b00);
   endrule
      
endmodule: mkTestbench_Tabulate3
   
    
endpackage : Tabulate3
