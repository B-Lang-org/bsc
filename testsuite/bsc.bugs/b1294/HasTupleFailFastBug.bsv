function c test(Tuple2#(a, Tuple2#(b, c)) in);
  Tuple2#(b, c) temp = tpl_2(in);
  return (tpl_2(temp));
endfunction

function f test2(Tuple2#(d, Tuple2#(e, f)) in) = test(in);

