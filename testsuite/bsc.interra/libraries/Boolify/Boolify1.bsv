package Boolify1;

import Boolify :: *;

function Bit #(6) add (Bit #(3) a, Bit #(3) b) ;
    return (zeroExtend(a)+zeroExtend(b));
endfunction: add

function  (Bit #(6)) boolified_add (Bit #(3) a, Bit #(3) b);
    return ((boolify (add)) (a,b)) ;
endfunction: boolified_add


interface IFC;
   method Bit #(6) start (Bit #(3) a, Bit #(3) b);
endinterface : IFC

module mkDesign_Boolify11 (IFC);
  method start (a,b);
     return (add (a,b));
  endmethod : start
endmodule : mkDesign_Boolify11

module mkDesign_Boolify1 (IFC);
  method start (a,b);
     return (boolified_add (a,b));
  endmethod : start
endmodule : mkDesign_Boolify1



module mkTestbench_Boolify1 ();

   IFC dut1();
   mkDesign_Boolify11 the_dut1 (dut1);
   IFC dut2();
   mkDesign_Boolify1 the_dut2 (dut2);

   Reg #(Bit #(7)) counter();
   mkReg #(0) the_counter(counter);
   
   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);
   
   Bit #(3) a = counter [2:0];
   Bit #(3) b = counter [5:3];

   rule always_true (True);
      counter <= counter + 1;
      $display ("A=%0d, B=%0d, Sum=%0d, Boolified Sum = %0d", a, b, dut1.start(a,b), dut2.start (a,b));
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
      
endmodule: mkTestbench_Boolify1
   
    

endpackage : Boolify1
