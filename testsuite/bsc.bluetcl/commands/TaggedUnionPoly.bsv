typedef union tagged {
  UInt#(k) Fin;
} Fin#(type n, type k);

typedef union tagged {
  Fin#(n,k) N;
  Fin#(s,k) S;
  Fin#(r,k) R;
} NSRK#(type n, type s, type r, type k);

