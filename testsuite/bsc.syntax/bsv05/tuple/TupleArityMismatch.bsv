// The arity of tuple(...) must match the declared Tuple#(...)

function Tuple#(Bool, Bool, Bool) f();
   return tuple(True, False);
endfunction
