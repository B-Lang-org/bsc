//----------------------------------------------------
//-- FileName : using 8'b0 instead of 8'b00000000
//-- Author   : Interra
//-- BugID    : 299
//-- CommandLine : bsc  bug.bsv
//-- Status : FIXED
//----------------------------------------------------

function Bit#(8) result (Bit#(8) in_data,Bit#(1) shift_dir);
Bit#(8) res;
       case (shift_dir)
             1'b0:   return(in_data + 1);
             default : return 8'b0;
       endcase
endfunction