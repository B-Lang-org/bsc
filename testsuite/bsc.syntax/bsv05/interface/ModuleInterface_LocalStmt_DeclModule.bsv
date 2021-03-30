
interface TopIfc;
    interface SubIfc s;
endinterface

interface SubIfc;
    method Module#(Reg#(Bool)) m();
endinterface

module sysModuleInterface_LocalStmt_DeclModule(TopIfc);
    interface SubIfc s;
        module [Module] mkM(Reg#(Bool));
            let _i <- mkRegU;
            return _i;
        endmodule

        method m = mkM;
    endinterface
endmodule
