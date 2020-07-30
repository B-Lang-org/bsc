
interface Foo;
    method Action bar;
endinterface

module sysIfcRuleWarning(Foo);
    Reg#(Bit#(8)) r();
    mkReg#(0) the_r(r);

    rule baz (True);
      action
        r <= r + 1;
      endaction
    endrule

    method bar;
      action
        r <= r + 1;
      endaction
    endmethod
endmodule

