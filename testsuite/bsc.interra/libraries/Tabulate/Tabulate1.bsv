package Tabulate1;

import Tabulate :: *;

function Bit #(6) add (Bit #(3) a, Bit #(3) b) ;
    return (zeroExtend(a)+zeroExtend(b));
endfunction: add

function  (Bit #(6)) tabulated_add (Bit #(3) a, Bit #(3) b);
    return ((tabulate (add)) (a,b)) ;
endfunction: tabulated_add


interface IFC;
   method Bit #(6) start (Bit #(3) a, Bit #(3) b);
endinterface : IFC

module mkDesign_Tabulate11 (IFC);
  method start (a,b);
     return (add (a,b));
  endmethod : start
endmodule : mkDesign_Tabulate11

module mkDesign_Tabulate1 (IFC);
  method start (a,b);
     return (tabulated_add (a,b));
  endmethod : start
endmodule : mkDesign_Tabulate1



module mkTestbench_Tabulate1 ();

   IFC dut1();
   mkDesign_Tabulate11 the_dut1 (dut1);
   IFC dut2();
   mkDesign_Tabulate1 the_dut2 (dut2);

   Reg #(Bit #(7)) counter();
   mkReg #(0) the_counter(counter);
   
   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);
   
   Bit #(3) a = counter [2:0];
   Bit #(3) b = counter [5:3];

   rule always_true (True);
      counter <= counter + 1;
      $display ("A=%d, B=%d, Sum=%d, Tabulated Sum = %d", a, b, dut1.start(a,b), dut2.start (a,b));
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
      
endmodule: mkTestbench_Tabulate1
   
    

endpackage : Tabulate1
