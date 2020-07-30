typedef struct { Bit#(n) fst; Bit#(n) snd; } Pair#(type n);

Pair#(8) a = Pair {fst:0, snd:1};

Pair#(1) x = ^ a;

