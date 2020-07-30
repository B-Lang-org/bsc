function Bool _(Bool x);
  return x;
endfunction

// Test that "_" can be used for Bool -> Bool
Bool y = _(True);

