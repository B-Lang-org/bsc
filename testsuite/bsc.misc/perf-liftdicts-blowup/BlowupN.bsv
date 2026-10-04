package BlowupN;

typeclass W#(type t);
   function Bit#(32) w(t x);
endtypeclass

instance W#(Bool);
   function w(x) = 1;
endinstance

instance W#(Tuple2#(a, b)) provisos (W#(a), W#(b));
   function w(x) = w(tpl_1(x)) + w(tpl_2(x));
endinstance

typedef Tuple2#(Bool, Bool) T1;
typedef Tuple2#(T1, T1) T2;
typedef Tuple2#(T2, T2) T3;
typedef Tuple2#(T3, T3) T4;
typedef Tuple2#(T4, T4) T5;
typedef Tuple2#(T5, T5) T6;
typedef Tuple2#(T6, T6) T7;
typedef Tuple2#(T7, T7) T8;
typedef Tuple2#(T8, T8) T9;
typedef Tuple2#(T9, T9) T10;
typedef Tuple2#(T10, T10) T11;
typedef Tuple2#(T11, T11) T12;
typedef Tuple2#(T12, T12) T13;
typedef Tuple2#(T13, T13) T14;
typedef Tuple2#(T14, T14) T15;
typedef Tuple2#(T15, T15) T16;

// forces the W#(T16) dictionary chain to be built and lifted,
// with no module elaboration: the cost isolated here is the
// fingerprint computation for the lifted dictionaries
function Bit#(32) topW(T16 x) = w(x);

endpackage
