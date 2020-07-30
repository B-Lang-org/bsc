
package MkArrayWCF;

import RegFile :: *;
import ConfigReg :: *;

interface Modified_Array;
    method Action upd (Bit #(3) a, Bit #(8) b);
    method Action ind (Bit #(3) a);
    method Bit #(8) sub ();
endinterface : Modified_Array

(* synthesize *)

module mkDesign_MkArrayWCF (Modified_Array); 
    RegFile #(Bit #(3) , Bit #(8)) dut_ifc();
    mkRegFileWCF #(0, 7) dut (dut_ifc);
    
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
    
             
endmodule : mkDesign_MkArrayWCF



//Testbench .
module mkTestbench_MkArrayWCF ();

    Modified_Array  dut();
    mkDesign_MkArrayWCF the_dut (dut);

    Reg #(Bit #(8)) counter();
    mkReg #(0) the_counter (counter);

    Reg #(Bool) fail();
    mkReg #(False) the_faile (fail);

    
    rule always_fire (True);
        counter <= counter + 1;
    endrule
    
    rule update_values (counter < 8);
        dut.upd(counter[2:0], counter [7:0]);
        $display ("Writing Value %d, at location %d", counter[2:0], counter [7:0]);
    endrule

    rule display_updated_values (counter >= 8);
        dut.ind (counter [2:0]);
        $display ("Cycle Number = %d, Value Read = %d, Index Provided = %d", counter, dut.sub (), counter [2:0]);
    endrule

    rule check_values (counter >= 10 && counter <=17);
        if (dut.sub() != (counter-10)[7:0])
          fail <= True;
    endrule

    rule end_sim (counter == 17);
        if (fail)
          $display ("Simulation Fails");
        else
          $display ("Simulation Passes");
        $finish (2'b00);
    endrule


    
  
endmodule : mkTestbench_MkArrayWCF
    



endpackage : MkArrayWCF
