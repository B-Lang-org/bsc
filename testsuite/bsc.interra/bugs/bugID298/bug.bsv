//----------------------------------------------------
//-- FileName : keyword "return" used as var name
//-- Author   : Interra
//-- BugID    : 298
//-- CommandLine : bsc  bug.bsv
//-- Status : ASSIGNED
//----------------------------------------------------
function Bit #(1) test();
Bit#(4) return;
return 1'b0;
endfunction: test