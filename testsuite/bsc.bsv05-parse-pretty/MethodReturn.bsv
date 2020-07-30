interface IMethodReturn;
    method Bool m();
endinterface

module sysMethodReturn(IMethodReturn);
    method m();
        m = True;
    endmethod
endmodule
