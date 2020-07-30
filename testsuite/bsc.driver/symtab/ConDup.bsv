import ConDup_Wrapper::*;
import ConDup_Leaf::*;

function Bool fn(U x);
  case (x) matches
     tagged C .b : return b;
  endcase
endfunction

