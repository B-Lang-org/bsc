typedef struct { Either#(String, b) result; } Exception#(type b);

instance Functor#(Exception);
  function \fmap (f, x);
    case (x.result) matches
      tagged Left .s: return(Exception { result : tagged Left s });
      tagged Right .v: return(Exception { result : tagged Right (f(v)) });
    endcase
  endfunction
endinstance
instance Applicative#(Exception);
  function \pure (v);
    return(Exception { result : tagged Right v });
  endfunction
  function \liftA2 (f, x, y);
    case (x.result) matches
      tagged Left .s: return(Exception { result : tagged Left s });
      tagged Right .v1:
        case (y.result) matches
          tagged Left .s: return(Exception { result : tagged Left s });
          tagged Right .v2: return(Exception { result : tagged Right (f(v1, v2)) });
        endcase
    endcase
  endfunction
endinstance
instance Monad#(Exception);
  function \bind (x, f);
    case (x.result) matches
      tagged Left .s: return(Exception { result : tagged Left s });
      tagged Right .v: return(f(v));
    endcase
  endfunction
endinstance
