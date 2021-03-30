interface IMethodCalledMethodII;
    method Bool m(Bool x);
endinterface

module sysMethodCalledMethodII(IMethodCalledMethodII);
    method Bool m(Bool x);
        m = True;
    endmethod
endmodule
