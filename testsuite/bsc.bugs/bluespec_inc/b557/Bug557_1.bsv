typedef Bit#(5) Src;
typedef Bit#(5) Dest;
typedef Bit#(5) Cond;
typedef Bit#(5) Addr;
typedef Bit#(5) Val;
typedef Bit#(32) Value;
typedef Bit#(10) Const;

typedef union tagged {
    struct { Dest rd; Src   ra; Src rb; } Add;
    struct { Cond cd; Addr  addr; }       Jz;
    struct { Dest rd; Addr  addr; }       Load;
    struct { Val  v;  Addr  addr; }       Store;
    struct { Dest rd; Const v; }          LoadC;
} Instr deriving (Bits);


module mkTest (Empty);
   Reg#(Instr) r();
   mkRegU the_r(r);
endmodule
