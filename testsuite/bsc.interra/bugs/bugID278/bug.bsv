//----------------------------------------------------
//-- FileName : bug.bsv
//-- Author   : Interra
//-- BugID    : 278
//-- CommandLine : bsc bug.bsv
//-- Status : ASSIGNED
//----------------------------------------------------
function Bool notfn(Bool x);
if(x) return False;
else  return True;
endfunction: notfn