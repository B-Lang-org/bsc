interface IMethodCalledMethodI;
    method Bool m();
endinterface

module sysMethodCalledMethodI(IMethodCalledMethodI);
    method Bool m();
        m = True;
    endmethod
endmodule
