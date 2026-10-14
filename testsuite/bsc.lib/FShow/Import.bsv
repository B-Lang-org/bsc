// Test that the FShow package can still be imported
// but with a warning that it is unnecessary

import FShow::*;

function Fmt fn();
  return fshow(True);
endfunction
