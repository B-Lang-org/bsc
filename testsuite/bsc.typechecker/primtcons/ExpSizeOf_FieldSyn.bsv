typedef UInt#(S#(t)) T#(type t);
typedef SizeOf#(t) S#(type t);

typedef struct {
    dataType data;
    T#(dataType) unused;
} Node#(type dataType) deriving (Bits, Eq);

(* synthesize *)
module sysExpSizeOf_FieldSyn();
    Reg#(Node#(UInt#(3)))  r_node  <- mkRegU;
    Reg#(UInt#(3))         r_data  <- mkRegU;

    rule r;
       r_data <= r_node.data;
    endrule
endmodule

