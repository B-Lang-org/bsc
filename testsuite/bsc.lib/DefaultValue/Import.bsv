// Test that the DefaultValue package can still be imported
// but with a warning that it is unnecessary

import DefaultValue::*;

function Bool fn();
  return defaultValue;
endfunction
