
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Action m1();
    method Action m2();
endinterface

module sysModuleInterface_LocalStmt_Between(TopIfc);
    Reg#(Bool) r <- mkReg(False);
    
    interface SubIfc s;
        method Action m1();
	   r <= !r;
        endmethod

        Bool tmp = True;

        method Action m();
            r <= tmp;
        endmethod
    endinterface
endmodule
