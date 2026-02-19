instance Functor#(Either#(String));
  function \fmap (f, x);
    case (x) matches
      tagged Left .s: return(tagged Left s);
      tagged Right .v: return(tagged Right (f(v)));
    endcase
  endfunction
endinstance
instance Applicative#(Either#(String));
  function \pure (v);
    return(tagged Right v);
  endfunction
  function \liftA2 (f, x, y);
    case (x) matches
      tagged Left .s: return(tagged Left s);
      tagged Right .v1:
        case (y) matches
          tagged Left .s: return(tagged Left s);
          tagged Right .v2: return(tagged Right (f(v1, v2)));
        endcase
    endcase
  endfunction
endinstance
instance Monad#(Either#(String));
  function \bind (x, f);
    case (x) matches
      tagged Left .s: return(tagged Left s);
      tagged Right .v: return(f(v));
    endcase
  endfunction
endinstance
