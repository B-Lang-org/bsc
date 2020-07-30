
typedef struct {
    dataType data;
    UInt#(SizeOf#(dataType)) unused;
} Node#(type dataType) deriving (Bits, Eq);

(* synthesize *)
module sysExpSizeOf_Field();
    Reg#(Node#(UInt#(3)))  r_node  <- mkRegU;
    Reg#(UInt#(3))         r_data  <- mkRegU;

    rule r;
       r_data <= r_node.data;
    endrule
endmodule

