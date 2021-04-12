function Bool f (int n);
  case (n) matches
    0: return True;
    // test that "_" binds here by getting a type failure
    ._: return _;
  endcase
endfunction
