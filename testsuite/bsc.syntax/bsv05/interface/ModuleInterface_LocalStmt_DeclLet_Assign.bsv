
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_DeclLet_Assign(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        let tmp;
        tmp = True;

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
