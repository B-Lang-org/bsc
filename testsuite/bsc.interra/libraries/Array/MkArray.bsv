
package MkArray;

import RegFile :: *;


//Check if a verilog is generated properly

module mkDesign_MkArray (RegFile #(Bit #(3) , Bit #(8))); 
    RegFile #(Bit #(3) , Bit #(8)) dut_ifc();
    mkRegFile #(0, 7) dut (dut_ifc);
    return dut_ifc;
endmodule : mkDesign_MkArray



//Testbench .
module mkTestbench_MkArray ();

    RegFile #(Bit #(3) , Bit #(8)) dut();
    mkRegFile #(0, 7) the_dut (dut);

    Reg #(Bit #(32)) counter();
    mkReg #(0) the_counter (counter);

    Reg #(Bool) fail();
    mkReg #(False) the_faile (fail);

    
    rule always_fire (True);
        counter <= counter + 1;
    endrule
    
    rule init_values (counter < 8);
        $display ("Initial Value: Index = %d, Data = %d", counter [2:0], dut.sub(counter [2:0]));
    endrule        
          
    rule update_values (counter >=8 && counter < 16);
        dut.upd(counter[2:0], counter [7:0]);
    endrule

    rule display_updated_values (counter >=16 && counter < 24);
        $display ("Updated Value: Index = %d, Data = %d", counter [2:0], dut.sub(counter [2:0]));
        if (dut.sub(counter [2:0]) != (counter-8)[7:0])
          fail <= True;
    endrule

    //See if reading array doesn't corrupt the values by any chance
    
    rule display_updated_values_again (counter >=24 && counter < 32);
        $display ("Updated Value: Index = %d, Data = %d", counter [2:0], dut.sub(counter [2:0]));
        if (dut.sub(counter [2:0]) != (counter-16)[7:0])
          fail <= True;
    endrule

    rule simultaneous_sub_update (counter == 32);
        $display ("Updating Second Value: Old Data = %d", dut.sub(1));
        dut.upd (1, 22);
        if (dut.sub(1) != 9)
          fail <= True;
    endrule
        
 
    rule check_updated_value (counter == 33) ;
        $display ("New Second Value : Data = %d", dut.sub (1));
        if (dut.sub(1) != 8'd22)
          fail <= True;
    endrule
 
    rule simultaneous_reads (counter == 34);
        $display ("Second Val=%d",dut.sub (2));
        $display ("Third Val=%d",dut.sub (3));
        $display ("Fourth Val=%d",dut.sub (4));
        $display ("Fifth Val=%d",dut.sub (5));
        $display ("Sixth Val=%d",dut.sub (6));
        if (dut.sub(2) != 10 ||dut.sub(3) != 11 ||dut.sub(4) != 12 ||dut.sub(5) != 13 ||dut.sub(6) != 14)
          fail <= True;
    endrule
  
    rule finish_off (counter ==35);
       if (fail==True) 
         $display ("Simulation Fails");
       else
         $display ("Simulation Passes");
         
       $finish(2'b00);
    endrule

  
endmodule : mkTestbench_MkArray
    



endpackage : MkArray
