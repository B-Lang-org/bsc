
package MkArrayWCFFile;

import RegFile :: *;
import RegFile :: *;
import ConfigReg :: *;

interface Modified_Array;
    method Action upd (Bit #(3) a, Bit #(8) b);
    method Action ind (Bit #(3) a);
    method Bit #(8) sub ();
endinterface : Modified_Array

(* synthesize *)

module mkDesign_MkArrayWCFFile (Modified_Array); 
    RegFile #(Bit #(3) , Bit #(8)) dut_ifc();
    mkRegFileWCFLoad #("input_file", 0, 7) dut (dut_ifc);
    
    Reg #(Bit #(8)) x();
    mkReg #(0) the_x(x);
    
    Reg #(Bit #(3)) y();
    mkConfigReg #(0) the_y(y);
    
    (* fire_when_enabled *)
    rule always_true (True);
        x <= dut_ifc.sub(y);
    endrule
    
    method upd (Bit #(3) a, Bit #(8) b);
        action
            dut_ifc.upd (a, b);
        endaction
    endmethod : upd

    method ind (Bit #(3) a);
        action
             y <= a;
        endaction
    endmethod : ind
    
    method sub ();
        return x;
    endmethod : sub
    
             
endmodule : mkDesign_MkArrayWCFFile



//Testbench .
module mkTestbench_MkArrayWCFFile ();

    Modified_Array  dut();
    mkDesign_MkArrayWCFFile the_dut (dut);

    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    Reg #(Bool) fail();
    mkReg #(False) the_faile (fail);

    
    rule always_fire (True);
        counter <= counter + 1;
    endrule
    
    rule display_values (counter >= 8 && counter <=17);
        dut.ind (counter [2:0]);
        $display ("Cycle Number = %d, Value Read = %h, Index Provided = %d", counter, dut.sub (), counter [2:0]);
    endrule

    rule check_values (counter >= 10 && counter <=17);
        case (counter)
            10 : if (dut.sub != 8'h01)
                    fail <= True;
            11 : if (dut.sub != 8'ha1)
                    fail <= True;
            12 : if (dut.sub != 8'hb1)
                    fail <= True;
            13 : if (dut.sub != 8'hc1)
                    fail <= True;
            14 : if (dut.sub != 8'hd1)
                    fail <= True;
            15 : if (dut.sub != 8'he1)
                    fail <= True;
            16 : if (dut.sub != 8'hf1)
                    fail <= True;
            17 : if (dut.sub != 8'h11)
                    fail <= True;
         endcase
    endrule

    rule update_values (counter >= 32 && counter < 40);
        dut.upd(counter[2:0], counter [7:0]);
        $display ("Cycle Number =%d, Writing Value %h, at location %d",counter, counter[7:0], counter [2:0]);
    endrule

    rule display_updated_values (counter >= 40);
        dut.ind (counter [2:0]);
        $display ("Cycle Number = %d, Value Read = %h, Index Provided = %d", counter, dut.sub (), counter [2:0]);
    endrule

    rule check_values_again (counter >= 42 && counter <=49);
        if (dut.sub() != (counter-10)[7:0])
          fail <= True;
    endrule



    rule end_sim (counter == 49);
        if (fail)
          $display ("Simulation Fails");
        else
          $display ("Simulation Passes");
        $finish (2'b00);
    endrule


    
  
endmodule : mkTestbench_MkArrayWCFFile
    



endpackage : MkArrayWCFFile
