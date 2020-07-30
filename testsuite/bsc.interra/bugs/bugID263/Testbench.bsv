/*
----------------------------------------------------
-- FileName : Testbench.bsv
-- Author   : Interra
-- BugID    : 263
-- CommandLine : bsc Testbench.bsv
-- Status : Fixed
----------------------------------------------------
*/

package Testbench;
import Printf :: *;

// This bug was about an old Printf package that no longer exists.
// The new Printf package has a similar issue, but it requires some
// contortions to make it show up; here, the compiler reports about
// an ambiguous type (the return type of "sprintf").
//
function Action status (Bool a);
action
  $display( (a ? sprintf ("True") : sprintf ("False")) );
endaction 
endfunction : status

endpackage : Testbench
