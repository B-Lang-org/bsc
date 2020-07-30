//Example how a small function can be exploded using Boolify

package Boolify4;

import Boolify :: *;

function Bit #(3) andfunc (Bit #(3) a, Bit #(3) b) ;
    return (primAnd (zeroExtend(a), zeroExtend(b)));
endfunction: andfunc

function  (Bit #(3)) boolified_andfunc (Bit #(3) a, Bit #(3) b);
    return ((boolify (andfunc)) (a,b)) ;
endfunction: boolified_andfunc


interface IFC;
   method Bit #(3) start (Bit #(3) a, Bit #(3) b);
endinterface : IFC

module mkDesign_Boolify41 (IFC);
  method start (a,b);
     return (andfunc (a,b));
  endmethod : start
endmodule : mkDesign_Boolify41

module mkDesign_Boolify4 (IFC);
  method start (a,b);
     return (boolified_andfunc (a,b));
  endmethod : start
endmodule : mkDesign_Boolify4



module mkTestbench_Boolify4 ();

   IFC dut1();
   mkDesign_Boolify41 the_dut1 (dut1);
   IFC dut2();
   mkDesign_Boolify4 the_dut2 (dut2);

   Reg #(Bit #(7)) counter();
   mkReg #(0) the_counter(counter);
   
   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);
   
   Bit #(3) a = counter [2:0];
   Bit #(3) b = counter [5:3];

   rule always_true (True);
      counter <= counter + 1;
      $display ("A=%b, B=%b, And=%b, Boolified And = %b", a, b, dut1.start(a,b), dut2.start (a,b));
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
      
endmodule: mkTestbench_Boolify4
   
    

endpackage : Boolify4
