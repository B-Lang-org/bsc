
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_DeclArrayAssign_AssignSub(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        Bool tmp[3] = { True, True, True };
        tmp[0] = False;

        method Action m();
            r <= tmp[0];
        endmethod
    endinterface
endmodule
