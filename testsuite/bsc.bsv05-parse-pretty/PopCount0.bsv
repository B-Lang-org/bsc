export popCountNaive;

export popCountTable;

export popCountTree;

export popCountWallace;

export LogK;

export popCountTableWallace;

export popCountTableTree;

import List::*;

import Vector::*;

import Wallace::*;

import Tabulate::*;

function val constant(val arg, sometype discardedArg);
   return arg;
endfunction: constant

function Bit#(s) plus(Bit#(s) x, Bit#(s) y);
  return (x + y);
endfunction: plus

function Bit#(m) popCountNaive(Bit#(n) x)
  provisos (Add#(a, 1, m));
  return (foldr(plus, 0, map(zExt1, unpack(x))));
endfunction: popCountNaive

function Bit#(m) zExt1(Bit#(1) x)
  provisos (Add#(m1, 1, m));
  return (zeroExtend(x));
endfunction: zExt1

function Bit#(m) popCountTable(Bit#(n) x)
  provisos (Add#(a, 1, m));
  return (tabulate(popCountNaive, x));
endfunction: popCountTable

function Bit#(m) popCountTree(Bit#(n) x)
  provisos (Add#(1, b, n), Add#(a, 1, m));
  return (fold(plus, map(zExt1, unpack(x))));
endfunction: popCountTree

function Bit#(m) popCountWallace(Bit#(n) x)
  provisos (Add#(1, a, m));
  return (wallaceAddBags((start((toList(unpack(x)))))));
endfunction: popCountWallace

function Vector#(n, List#(Bit#(1))) start(List#(Bit#(1)) bs)
  provisos (Add#(1, m, n));
  return (cons(bs, map(constant(Nil), genList)));
endfunction: start

typedef 8 K;

typedef 4 LogK;

function Bit#(m) popCountTableWallace(Bit#(n) x)
  provisos (Add#(LogK, k, m));
  return (wallaceAdd((List::map(popCK, splitInKs(0, x)))));
endfunction: popCountTableWallace

function Bit#(m) popCountTableTree(Bit#(n) x)
  provisos (Add#(a, LogK, m));
  return (List::fold(plus, List::map(zeroExtend, List::map(popCK, splitInKs(0, x)))));
endfunction: popCountTableTree

(* noinline *)

function Bit#(LogK) popCK(Bit#(K) x);
  return (popCountTable(x));
endfunction: popCK

function List#(Bit#(k)) splitInKs(Nat i, Bit#(n) bs);
  begin
    Nat ii =  min(fromInteger(valueOf(n)), (i + fromInteger(valueOf(k))));
    return (i == ii ? Nil : Cons(bs[ii - 1:i], splitInKs(ii, bs)));
  end
endfunction: splitInKs


