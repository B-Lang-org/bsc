package Test;

import RegFile :: *;

//Checking for arrays with negative index

module mkTestbench ();

    RegFile #(Int #(3) , Bit #(8)) dut();
    mkRegFile #(-3, 2) the_dut (dut);

    Reg #(Bit #(32)) counter();
    mkReg #(0) the_counter (counter);

    rule always_fire (True);
        counter <= counter + 1;
    endrule
    
    rule update_values (counter == 1);
        dut.upd(-2, 5);
    endrule

    rule read_value (counter == 2);
        $display ("Updated Value = %d", dut.sub(-2));
    endrule

  
endmodule : mkTestbench


endpackage : Test
