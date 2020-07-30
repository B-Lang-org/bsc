
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_DeclArray_ForLoop(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        Bool tmp[3];
        for (Integer i = 0; i < 3; i = i + 1) tmp[i] = True;

        method Action m();
            r <= tmp[0] && tmp[1] && tmp[2];
        endmethod
    endinterface
endmodule
