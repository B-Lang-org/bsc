function Bool _(Bool x);
  return x;
endfunction

// Test that "_" has the right type by expecting a failure on mis-use
Bool y = _ ;

