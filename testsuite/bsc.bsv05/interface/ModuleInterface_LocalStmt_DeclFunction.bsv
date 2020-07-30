
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_DeclFunction(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        function Bool fn();
            return True;
        endfunction

        method Action m();
            r <= fn;
        endmethod
    endinterface
endmodule
