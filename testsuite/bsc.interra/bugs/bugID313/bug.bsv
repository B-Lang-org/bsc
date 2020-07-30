//----------------------------------------------------
//-- FileName : Two parameters to function having same name
//-- Author   : Interra
//-- BugID    : 313
//-- CommandLine : bsc  bug.bsv
//-- Status : FIXED
//----------------------------------------------------
function Integer myFunc(Integer abc,Integer abc);
if(abc == 1)
return 0;
else
return 1;
endfunction: myFunc