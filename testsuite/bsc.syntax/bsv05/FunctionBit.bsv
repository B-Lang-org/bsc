function bit test(bit x);
  return(~x);
endfunction

function bit[3:0] test2(bit[2:0] x);
  return(zeroExtend(x));
endfunction

typedef function bit[10:0] f(bit[10:0] x) Func;

function Func twice(function bit[10:0] f(bit[10:0] x));
  function f2(x);
    return(f(f(x)));
  endfunction
  return(f2);
endfunction



