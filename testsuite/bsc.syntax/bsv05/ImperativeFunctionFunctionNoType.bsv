function Bool f(Bool x, Bool y);
  function g(a, b);
    g = a || b;
  endfunction: g
  f = g(x, y);
endfunction: f
