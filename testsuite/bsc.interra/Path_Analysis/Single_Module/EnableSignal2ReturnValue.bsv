//Creates a cycle from Enable Signal of a method
//to its return value

package EnableSignal2ReturnValue;

(* synthesize *)
module mkEnableSignal2ReturnValue (Empty);

    RWire#(Bit#(2)) x();
    mkRWire the_x(x);

    rule flip (isJust (x.wget));
        x.wset (0);
    endrule

endmodule

endpackage
