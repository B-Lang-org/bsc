
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_If(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        Bool tmp = True;
        if (r)
	   tmp = False;

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
