// A rule's predicate depends on the rule's firing.
// Should report an error with -verilog flag
// Cycle from WILL_FIRE to CAN_FIRE

package WillFire2CanFire;

interface ArithIO ;
    method Bit #(2) getOutput();
endinterface: ArithIO

(* synthesize *)
module [Module] mkWillFire2CanFire(ArithIO);

    RWire#(Bit #(2)) x();
    mkRWire the_x(x);

    Bit #(2) temp1 = x.wget matches tagged Just {.x} ? x: 0;
    Bit #(2) temp2 = (temp1 == 0) ? 3: 1;

    rule rule_1 (temp2 == 1) ;
        x.wset (1);
    endrule

    method getOutput();
        return (unJust (x.wget ));
    endmethod

endmodule

endpackage 

