
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_DeclAssignLet(TopIfc);
    Reg#(Bool) r <- mkReg(False);
    
    interface SubIfc s;
        let tmp = True;

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
