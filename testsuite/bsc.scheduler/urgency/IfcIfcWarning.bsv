
interface Foo;
    method Action bar;
    method Action baz;
endinterface

module sysIfcIfcWarning(Foo);
    Reg#(Bit#(8)) r();
    mkReg#(0) the_r(r);

    method bar;
      action
        r <= r + 1;
      endaction
    endmethod

    method baz;
      action
        r <= r + 2;
      endaction
    endmethod
endmodule

