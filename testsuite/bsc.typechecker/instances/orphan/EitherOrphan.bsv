instance Monad#(Either#(String));
  function \bind (x, f);
    case (x) matches 
      tagged Left .s: return(tagged Left s);
      tagged Right .v: return(f(v));
    endcase
  endfunction
  function \return (v);
    return(tagged Right v);
  endfunction
endinstance
 