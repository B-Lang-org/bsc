//----------------------------------------------------
//-- FileName : returning from diff paths of if
//-- Author   : Interra
//-- BugID    : 198
//-- CommandLine : bsc  bug.bsv
//-- Status : FIXED
//----------------------------------------------------
function bit[3:0] f(Bool cond);
  if (cond)
    return 3;
  else
    return 5;
endfunction