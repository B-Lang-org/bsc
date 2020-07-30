
typedef struct {
    Bool f1;
    Bool f2;
} S deriving (Eq, Bits);

interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_Decl_AssignField(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        S tmp;
        tmp.f1 = False;
	tmp.f2 = True;

        method Action m();
            r <= tmp.f1;
        endmethod
    endinterface
endmodule
