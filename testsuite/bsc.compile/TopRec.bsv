import List::*;

function Integer inc(Integer x);
  return (x + 1);
endfunction: inc

List#(Integer) evens;
evens = cons(0,map(inc, odds));

List#(Integer) odds;
odds = map(inc, evens);

