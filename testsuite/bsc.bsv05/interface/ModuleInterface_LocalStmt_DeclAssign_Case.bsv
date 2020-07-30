
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m();
endinterface

module sysModuleInterface_LocalStmt_Case(TopIfc);
    Reg#(Bool) r <- mkReg(False);

    interface SubIfc s;
        Bool tmp = True;
        case (r)
	   True : tmp = False;
	   False : tmp = True;
	endcase

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
