typedef struct { Bit#(1) fst; Bit#(2) snd; } Pair;

Pair a = Pair {fst:0, snd:1};
Pair b = Pair {fst:1, snd:0};

Pair x = a ^ b;

