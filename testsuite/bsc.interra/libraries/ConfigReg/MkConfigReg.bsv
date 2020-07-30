package mkConfigReg;

import ConfigReg :: *;


interface Inpt;
    method Action inp(Int #(8) x);
    method Int #(8) outpt();
endinterface: Inpt

(* synthesize *)
module mkDesign_MkConfigReg(Inpt);

    Reg#(Int #(8)) x();
    mkConfigReg#(0) the_x(x);

    Reg#(Int #(8)) y();
    mkReg#(0) the_y(y);
    
    
  // (* fire_when_enabled *)
    rule assignxy (True);
        y <= x;
    endrule


    method Action inp(Int #(8) a);
        action
            x <= a;
        endaction
    endmethod: inp

    method Int #(8) outpt();
         outpt = y;
    endmethod: outpt

endmodule: mkDesign_MkConfigReg

module mkTestbench_MkConfigReg();

     Inpt dut();
     mkDesign_MkConfigReg the_dut(dut);

     Reg #(Int #(8)) counter();
     mkReg #(0) the_counter(counter);

     rule counter_increment (True);
         counter <= counter + 1;
     endrule

     rule show_values (counter < 100);
          $display ("Y = %d", dut.outpt);
     endrule

     rule call_dut (True);
       if (counter < 20) 
           dut.inp (20);
       else if (counter < 40)
           dut.inp (40);
       else if (counter < 80)
           dut.inp (80);
       else if (counter < 100)
           dut.inp (100);
       else
           $finish (2'b00);
     endrule

endmodule : mkTestbench_MkConfigReg
     
endpackage :mkConfigReg
