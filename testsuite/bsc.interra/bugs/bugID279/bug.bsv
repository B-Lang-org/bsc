//----------------------------------------------------
//-- FileName : bug.bsv
//-- Author   : Interra
//-- BugID    : 279
//-- CommandLine : bsc bug.bsv
//-- Status : ASSIGNED
//----------------------------------------------------
function Bool notfct (Bool x);
if (x) notfct  =  False;
else   notfct  =  True;
endfunction: notfct
