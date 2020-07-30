package Boolify2;

import Boolify :: *;

function Bit #(7) mult (Bit #(3) a, Bit #(3) b) ;
    return (zeroExtend(a)*zeroExtend(b));
endfunction: mult

function  (Bit #(7)) boolified_mult (Bit #(3) a, Bit #(3) b);
    return ((boolify (mult)) (a,b)) ;
endfunction: boolified_mult


interface IFC;
   method Bit #(7) start (Bit #(3) a, Bit #(3) b);
endinterface : IFC

module mkDesign_Boolify21 (IFC);
  method start (a,b);
     return (mult (a,b));
  endmethod : start
endmodule : mkDesign_Boolify21

module mkDesign_Boolify2 (IFC);
  method start (a,b);
     return (boolified_mult (a,b));
  endmethod : start
endmodule : mkDesign_Boolify2



module mkTestbench_Boolify2 ();

   IFC dut1();
   mkDesign_Boolify21 the_dut1 (dut1);
   IFC dut2();
   mkDesign_Boolify2 the_dut2 (dut2);

   Reg #(Bit #(7)) counter();
   mkReg #(0) the_counter(counter);
   
   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);
   
   Bit #(3) a = counter [2:0];
   Bit #(3) b = counter [5:3];

   rule always_true (True);
      counter <= counter + 1;
      $display ("A=%0d, B=%0d, Product=%0d, Boolified Product = %0d", a, b, dut1.start(a,b), dut2.start (a,b));
      if (dut1.start(a,b) != dut2.start(a,b))
        fail <= True;
   endrule

   rule result (counter [6:6] == 1);
      if (fail) 
         $display ("Simulation Fails");
      else
         $display ("Simulation Passes");
      $finish (2'b00);
   endrule
      
endmodule: mkTestbench_Boolify2
   
    

endpackage : Boolify2
