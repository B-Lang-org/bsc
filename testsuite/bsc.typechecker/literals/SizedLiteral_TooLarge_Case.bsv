function Bool fn (Bit#(11) x);
   case (x)
      11'h800 : return True;
      default : return False;
   endcase
endfunction

