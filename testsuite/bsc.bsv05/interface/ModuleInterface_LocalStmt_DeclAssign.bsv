
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_DeclAssign(TopIfc);
    Reg#(Bool) r <- mkReg(False);
    
    interface SubIfc s;
        Bool tmp = True;

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
