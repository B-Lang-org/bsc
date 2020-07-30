package Tabulate2;

import Tabulate :: *;

function Bit #(6) mult (Bit #(3) a, Bit #(3) b) ;
    return (zeroExtend(a)*zeroExtend(b));
endfunction: mult

function  (Bit #(6)) tabulated_mult (Bit #(3) a, Bit #(3) b);
    return (tabulate (mult (a),b)) ;
endfunction: tabulated_mult


interface IFC;
   method Bit #(6) start (Bit #(3) a, Bit #(3) b);
endinterface : IFC

module mkDesign_Tabulate21 (IFC);
  method start (a,b);
     return (mult (a,b));
  endmethod : start
endmodule : mkDesign_Tabulate21

module mkDesign_Tabulate2 (IFC);
  method start (a,b);
     return (tabulated_mult (a,b));
  endmethod : start
endmodule : mkDesign_Tabulate2



module mkTestbench_Tabulate2 ();

   IFC dut1();
   mkDesign_Tabulate21 the_dut1 (dut1);
   IFC dut2();
   mkDesign_Tabulate2 the_dut2 (dut2);

   Reg #(Bit #(7)) counter();
   mkReg #(0) the_counter(counter);
   
   Reg #(Bool) fail();
   mkReg #(False) the_fail(fail);
   
   Bit #(3) a = counter [2:0];
   Bit #(3) b = counter [5:3];

   rule always_true (True);
      counter <= counter + 1;
      $display ("A=%d, B=%d, Product=%d, Tabulated Product = %d", a, b, dut1.start(a,b), dut2.start (a,b));
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
      
endmodule: mkTestbench_Tabulate2
   
    

endpackage : Tabulate2
