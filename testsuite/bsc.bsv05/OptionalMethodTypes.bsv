interface IOptionalMethodTypes;
    method Bool m1(Bool x, Bool y);
    method Bool m2(Bool x, Bool y);
endinterface

module sysOptionalMethodTypes(IOptionalMethodTypes);
    method m1(x,y);
        m1 = x || y;
    endmethod
    method Bool m2(Bool x, Bool y);
        m2 = x || y;
    endmethod
endmodule
