package WallaceLib;

// Library of procedures useful for constructing Wallace adders

import List::*;

import ListN::*;

typedef Bit#(1) Bit1;
typedef List#(Bit1) BitBag;

function Bool notDone(List#(Bit1) l);
   return(length(l) > 1);
endfunction: notDone

// continue applying a function to the input until the input 
// predicate becomes false
function a doWhile(function Bool p(a x1), function a f(a x1), a x);
   return (p(x) ? doWhile(p, f, f(x)) : x);
endfunction: doWhile

// add a list of m-bit numbers to get an n-bit result
// note n must be greater than or equal to m
// because of the Add#(m,k,n) proviso
function Bit#(n) wallaceAdd(List#(Bit#(m)) ms) provisos (Add#(m,k,n));
  return (wallaceAddBags(padWith(Nil,transposeLN(List::map(unpack,ms)))));
endfunction: wallaceAdd

// perform Wallace addition on n BitBags to get an n-bit result
function Bit#(n) wallaceAddBags(ListN#(n, BitBag) bags);
   return(pack(map(head0,doWhile(any(notDone),wallaceStep,bags))));
endfunction: wallaceAddBags

// combine n pairs of BitBags to get n resulting BitBags
function ListN#(n, BitBag) combine(ListN#(n, Tuple2#(BitBag, BitBag)) xys);
    return (zipWith(List::append, map(tpl_2, xys), init(cons(Nil, map(tpl_1, xys)))));
endfunction: combine

// stateful combination needs to reverse the BitBags so that
// the most significant bits move to the front of the list
function ListN#(n, BitBag) statefulCombine(ListN#(n, Tuple2#(BitBag, BitBag)) xys);
    return (zipWith(List::append, map(compose(List::reverse,tpl_2),xys),
                                  init(cons(Nil, map(compose(List::reverse,tpl_1),xys)))));
endfunction: statefulCombine

// grab the first bit in the BitBag (or 0 if the BitBag is empty)
function Bit1 head0(BitBag bag);
    case (decodeList(bag)) matches
      tagged Valid { .x, .* } : return x;
      tagged Invalid          : return 0;
    endcase
endfunction: head0       

// perform a single step of the Wallace algorithm on
// the bits in ns, recursively accumulating the new 
// BitBags in ms and ls (which will be combined)
function Tuple2#(BitBag, BitBag) step(BitBag ms, BitBag ls, BitBag ns);
   case (length(ns)) matches
      0       : return(tuple2(ms, ls));
      1       : return(tuple2(ms, List::cons(ns[0],ls)));
      2       : begin
                    Tuple2#(Bit1, Bit1) tmp = halfAdd(ns[0], ns[1]);
                    return(tuple2(List::cons(tpl_1(tmp),ms),
                                  List::cons(tpl_2(tmp),ls)));
                end
      default : begin
                    Tuple2#(Bit1, Bit1) tmp2 = fullAdd(ns[0],ns[1],ns[2]);
                    return(step(List::cons(tpl_1(tmp2), ms),
                                List::cons(tpl_2(tmp2), ls), drop(3,ns)));
                end
   endcase
endfunction: step    

function ListN#(n, BitBag) wallaceStep(ListN#(n, BitBag) ns);
   return combine(map(step(Nil,Nil), ns));
endfunction: wallaceStep

function ListN#(n, BitBag) statefulWallaceStep(ListN#(n, BitBag) ns);
   return statefulCombine(map(step(Nil,Nil), ns));
endfunction: statefulWallaceStep

function Tuple2#(Bit1, Bit1) halfAdd(Bit1 a, Bit1 b);
   return (tuple2(a&b, a^b));
endfunction: halfAdd

function Tuple2#(Bit1, Bit1) fullAdd(Bit1 a, Bit1 b, Bit1 c);
   return tuple2(a&b | b&c | c&a, a^b^c);
endfunction: fullAdd
 
function ListN#(n, a) padWith(a p, ListN#(m, a) xs)
  provisos(Add#(m,k,n));
  return (append(xs, map(constFn(p), genList)));
endfunction: padWith 
 
function ListN#(n, Bit1) padToNBits(ListN#(m,Bit1) xs) provisos (Add#(m,k,n));
  return(append(xs,ListN#(k,Bit1)'(genWith(constFn(0)))));
endfunction: padToNBits 

function ListN#(n, Bit1) padListToListN(List#(Bit1) xs);
  return(toListN(List::append(xs,List::map(constFn(0),(List::upto(1, valueOf(n) - length(xs)))))));
endfunction: padListToListN

endpackage
