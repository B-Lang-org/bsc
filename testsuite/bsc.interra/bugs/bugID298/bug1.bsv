//----------------------------------------------------
//-- FileName : keyword "return" used as function name
//-- Author   : Interra
//-- BugID    : 298
//-- CommandLine : bsc  bug1.bsv
//-- Status : ASSIGNED
//----------------------------------------------------
function Bit #(1) return();
Bit#(4) return;
return 1'b0;
endfunction: return
