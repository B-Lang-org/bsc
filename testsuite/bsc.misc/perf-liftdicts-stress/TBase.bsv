package TBase;
typeclass TK#(type t); function Bit#(8) tag(t x); endtypeclass
typeclass TDK#(type t); function Bit#(8) dtag(t x); endtypeclass
instance TDK#(t) provisos (TK#(t)); function dtag(x) = tag(x); endinstance
typeclass B_#(type t); function Bit#(8) getB(t x); endtypeclass
typeclass S_#(type t); function Bit#(8) getS(t x); endtypeclass
instance S_#(t) provisos (B_#(t)); function getS(x) = getB(x); endinstance

typeclass CC#(type t); function Bit#(8) getC(t x); endtypeclass
typedef struct { t g; } Box#(type t);
instance CC#(Box#(t)) provisos (CC#(t)); function getC(x) = getC(x.g); endinstance

typedef struct { Bit#(8) f; } X0#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X1#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X2#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X3#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X4#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X5#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X6#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X7#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X8#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X9#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X10#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X11#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X12#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X13#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X14#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X15#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X16#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X17#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X18#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X19#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X20#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X21#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X22#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X23#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X24#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X25#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X26#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X27#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X28#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X29#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X30#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X31#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X32#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X33#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X34#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X35#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X36#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X37#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X38#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X39#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X40#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X41#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X42#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X43#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X44#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X45#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X46#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X47#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X48#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X49#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X50#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X51#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X52#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X53#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X54#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X55#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X56#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X57#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X58#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X59#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X60#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X61#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X62#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X63#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X64#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X65#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X66#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X67#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X68#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X69#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X70#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X71#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X72#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X73#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X74#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X75#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X76#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X77#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X78#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X79#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X80#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X81#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X82#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X83#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X84#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X85#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X86#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X87#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X88#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X89#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X90#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X91#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X92#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X93#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X94#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X95#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X96#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X97#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X98#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X99#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X100#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X101#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X102#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X103#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X104#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X105#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X106#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X107#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X108#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X109#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X110#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X111#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X112#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X113#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X114#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X115#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X116#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X117#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X118#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X119#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X120#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X121#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X122#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X123#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X124#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X125#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X126#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X127#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X128#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X129#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X130#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X131#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X132#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X133#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X134#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X135#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X136#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X137#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X138#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X139#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X140#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X141#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X142#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X143#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X144#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X145#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X146#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X147#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X148#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X149#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X150#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X151#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X152#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X153#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X154#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X155#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X156#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X157#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X158#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X159#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X160#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X161#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X162#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X163#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X164#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X165#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X166#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X167#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X168#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X169#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X170#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X171#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X172#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X173#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X174#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X175#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X176#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X177#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X178#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X179#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X180#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X181#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X182#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X183#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X184#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X185#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X186#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X187#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X188#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X189#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X190#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X191#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X192#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X193#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X194#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X195#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X196#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X197#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X198#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } X199#(type a0, type a1, type a2, type a3, type a4, type a5, type a6, type a7);
typedef struct { Bit#(8) f; } W0;
instance B_#(W0); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W1;
instance B_#(W1); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W2;
instance B_#(W2); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W3;
instance B_#(W3); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W4;
instance B_#(W4); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W5;
instance B_#(W5); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W6;
instance B_#(W6); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W7;
instance B_#(W7); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W8;
instance B_#(W8); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W9;
instance B_#(W9); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W10;
instance B_#(W10); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W11;
instance B_#(W11); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W12;
instance B_#(W12); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W13;
instance B_#(W13); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W14;
instance B_#(W14); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W15;
instance B_#(W15); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W16;
instance B_#(W16); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W17;
instance B_#(W17); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W18;
instance B_#(W18); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W19;
instance B_#(W19); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W20;
instance B_#(W20); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W21;
instance B_#(W21); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W22;
instance B_#(W22); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W23;
instance B_#(W23); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W24;
instance B_#(W24); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W25;
instance B_#(W25); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W26;
instance B_#(W26); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W27;
instance B_#(W27); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W28;
instance B_#(W28); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W29;
instance B_#(W29); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W30;
instance B_#(W30); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W31;
instance B_#(W31); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W32;
instance B_#(W32); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W33;
instance B_#(W33); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W34;
instance B_#(W34); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W35;
instance B_#(W35); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W36;
instance B_#(W36); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W37;
instance B_#(W37); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W38;
instance B_#(W38); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W39;
instance B_#(W39); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W40;
instance B_#(W40); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W41;
instance B_#(W41); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W42;
instance B_#(W42); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W43;
instance B_#(W43); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W44;
instance B_#(W44); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W45;
instance B_#(W45); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W46;
instance B_#(W46); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W47;
instance B_#(W47); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W48;
instance B_#(W48); function getB(x) = x.f; endinstance
typedef struct { Bit#(8) f; } W49;
instance B_#(W49); function getB(x) = x.f; endinstance

typedef struct { Bit#(8) f; } Y0;
instance CC#(Y0); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y1;
instance CC#(Y1); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y2;
instance CC#(Y2); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y3;
instance CC#(Y3); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y4;
instance CC#(Y4); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y5;
instance CC#(Y5); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y6;
instance CC#(Y6); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y7;
instance CC#(Y7); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y8;
instance CC#(Y8); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y9;
instance CC#(Y9); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y10;
instance CC#(Y10); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y11;
instance CC#(Y11); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y12;
instance CC#(Y12); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y13;
instance CC#(Y13); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y14;
instance CC#(Y14); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y15;
instance CC#(Y15); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y16;
instance CC#(Y16); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y17;
instance CC#(Y17); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y18;
instance CC#(Y18); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y19;
instance CC#(Y19); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y20;
instance CC#(Y20); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y21;
instance CC#(Y21); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y22;
instance CC#(Y22); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y23;
instance CC#(Y23); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y24;
instance CC#(Y24); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y25;
instance CC#(Y25); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y26;
instance CC#(Y26); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y27;
instance CC#(Y27); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y28;
instance CC#(Y28); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y29;
instance CC#(Y29); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y30;
instance CC#(Y30); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y31;
instance CC#(Y31); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y32;
instance CC#(Y32); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y33;
instance CC#(Y33); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y34;
instance CC#(Y34); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y35;
instance CC#(Y35); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y36;
instance CC#(Y36); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y37;
instance CC#(Y37); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y38;
instance CC#(Y38); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y39;
instance CC#(Y39); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y40;
instance CC#(Y40); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y41;
instance CC#(Y41); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y42;
instance CC#(Y42); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y43;
instance CC#(Y43); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y44;
instance CC#(Y44); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y45;
instance CC#(Y45); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y46;
instance CC#(Y46); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y47;
instance CC#(Y47); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y48;
instance CC#(Y48); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y49;
instance CC#(Y49); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y50;
instance CC#(Y50); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y51;
instance CC#(Y51); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y52;
instance CC#(Y52); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y53;
instance CC#(Y53); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y54;
instance CC#(Y54); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y55;
instance CC#(Y55); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y56;
instance CC#(Y56); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y57;
instance CC#(Y57); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y58;
instance CC#(Y58); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y59;
instance CC#(Y59); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y60;
instance CC#(Y60); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y61;
instance CC#(Y61); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y62;
instance CC#(Y62); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y63;
instance CC#(Y63); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y64;
instance CC#(Y64); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y65;
instance CC#(Y65); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y66;
instance CC#(Y66); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y67;
instance CC#(Y67); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y68;
instance CC#(Y68); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y69;
instance CC#(Y69); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y70;
instance CC#(Y70); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y71;
instance CC#(Y71); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y72;
instance CC#(Y72); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y73;
instance CC#(Y73); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y74;
instance CC#(Y74); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y75;
instance CC#(Y75); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y76;
instance CC#(Y76); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y77;
instance CC#(Y77); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y78;
instance CC#(Y78); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y79;
instance CC#(Y79); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y80;
instance CC#(Y80); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y81;
instance CC#(Y81); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y82;
instance CC#(Y82); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y83;
instance CC#(Y83); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y84;
instance CC#(Y84); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y85;
instance CC#(Y85); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y86;
instance CC#(Y86); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y87;
instance CC#(Y87); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y88;
instance CC#(Y88); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y89;
instance CC#(Y89); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y90;
instance CC#(Y90); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y91;
instance CC#(Y91); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y92;
instance CC#(Y92); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y93;
instance CC#(Y93); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y94;
instance CC#(Y94); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y95;
instance CC#(Y95); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y96;
instance CC#(Y96); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y97;
instance CC#(Y97); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y98;
instance CC#(Y98); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y99;
instance CC#(Y99); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y100;
instance CC#(Y100); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y101;
instance CC#(Y101); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y102;
instance CC#(Y102); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y103;
instance CC#(Y103); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y104;
instance CC#(Y104); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y105;
instance CC#(Y105); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y106;
instance CC#(Y106); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y107;
instance CC#(Y107); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y108;
instance CC#(Y108); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y109;
instance CC#(Y109); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y110;
instance CC#(Y110); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y111;
instance CC#(Y111); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y112;
instance CC#(Y112); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y113;
instance CC#(Y113); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y114;
instance CC#(Y114); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y115;
instance CC#(Y115); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y116;
instance CC#(Y116); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y117;
instance CC#(Y117); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y118;
instance CC#(Y118); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y119;
instance CC#(Y119); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y120;
instance CC#(Y120); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y121;
instance CC#(Y121); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y122;
instance CC#(Y122); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y123;
instance CC#(Y123); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y124;
instance CC#(Y124); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y125;
instance CC#(Y125); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y126;
instance CC#(Y126); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y127;
instance CC#(Y127); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y128;
instance CC#(Y128); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y129;
instance CC#(Y129); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y130;
instance CC#(Y130); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y131;
instance CC#(Y131); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y132;
instance CC#(Y132); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y133;
instance CC#(Y133); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y134;
instance CC#(Y134); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y135;
instance CC#(Y135); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y136;
instance CC#(Y136); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y137;
instance CC#(Y137); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y138;
instance CC#(Y138); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y139;
instance CC#(Y139); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y140;
instance CC#(Y140); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y141;
instance CC#(Y141); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y142;
instance CC#(Y142); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y143;
instance CC#(Y143); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y144;
instance CC#(Y144); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y145;
instance CC#(Y145); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y146;
instance CC#(Y146); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y147;
instance CC#(Y147); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y148;
instance CC#(Y148); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y149;
instance CC#(Y149); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y150;
instance CC#(Y150); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y151;
instance CC#(Y151); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y152;
instance CC#(Y152); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y153;
instance CC#(Y153); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y154;
instance CC#(Y154); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y155;
instance CC#(Y155); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y156;
instance CC#(Y156); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y157;
instance CC#(Y157); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y158;
instance CC#(Y158); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y159;
instance CC#(Y159); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y160;
instance CC#(Y160); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y161;
instance CC#(Y161); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y162;
instance CC#(Y162); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y163;
instance CC#(Y163); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y164;
instance CC#(Y164); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y165;
instance CC#(Y165); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y166;
instance CC#(Y166); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y167;
instance CC#(Y167); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y168;
instance CC#(Y168); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y169;
instance CC#(Y169); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y170;
instance CC#(Y170); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y171;
instance CC#(Y171); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y172;
instance CC#(Y172); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y173;
instance CC#(Y173); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y174;
instance CC#(Y174); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y175;
instance CC#(Y175); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y176;
instance CC#(Y176); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y177;
instance CC#(Y177); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y178;
instance CC#(Y178); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y179;
instance CC#(Y179); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y180;
instance CC#(Y180); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y181;
instance CC#(Y181); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y182;
instance CC#(Y182); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y183;
instance CC#(Y183); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y184;
instance CC#(Y184); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y185;
instance CC#(Y185); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y186;
instance CC#(Y186); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y187;
instance CC#(Y187); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y188;
instance CC#(Y188); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y189;
instance CC#(Y189); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y190;
instance CC#(Y190); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y191;
instance CC#(Y191); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y192;
instance CC#(Y192); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y193;
instance CC#(Y193); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y194;
instance CC#(Y194); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y195;
instance CC#(Y195); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y196;
instance CC#(Y196); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y197;
instance CC#(Y197); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y198;
instance CC#(Y198); function getC(x) = x.f; endinstance
typedef struct { Bit#(8) f; } Y199;
instance CC#(Y199); function getC(x) = x.f; endinstance
endpackage
