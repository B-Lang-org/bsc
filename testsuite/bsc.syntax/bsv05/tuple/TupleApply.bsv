// Only the first argument list of tuple(...) is the tuple; a further list
// applies the tuple, which is a type error (not a 3-tuple)

function Tuple#(Bool, Bool, Bool) f();
   return tuple(True, False)(True);
endfunction
