
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_If(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    Bool tmp = True;

    interface SubIfc s;
        if (r)
	   tmp = False;

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
