
typedef struct {
    dataType data;
    UInt#(TSub#(TSub#(8,SizeOf#(dataType)), 8)) unused;
} Node#(type dataType) deriving (Bits);

module sysContextReductionRemoveImpliedCloseFD();
    Reg#(Node#(UInt#(3))) rg <- mkRegU;
endmodule

