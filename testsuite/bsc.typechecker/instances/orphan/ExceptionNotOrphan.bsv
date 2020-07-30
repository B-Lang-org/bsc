typedef struct { Either#(String, b) result; } Exception#(type b);

instance Monad#(Exception);
  function \bind (x, f);
    case (x.result) matches 
      tagged Left .s: return(tagged Exception { result : tagged Left s });
      tagged Right .v: return(f(v));
    endcase
  endfunction
  function \return (v);
    return(tagged Exception { result : tagged Right v });
  endfunction
endinstance
 