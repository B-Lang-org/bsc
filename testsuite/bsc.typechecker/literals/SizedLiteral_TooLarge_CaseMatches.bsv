function Bool fn (Maybe#(Bit#(11)) m);
   case (m) matches
      tagged Valid 11'h800 : return True;
      default : return False;
   endcase
endfunction

