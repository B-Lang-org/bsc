// Test that "_" has the right type by expecting a failure on mis-use
function Bit#(8) fn(Bool _);
  return _;
endfunction
