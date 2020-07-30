function Bit#(4) matchHex(Bit#(32) b);
  case (b) matches
    12?4 : return 'b0010;
    123? : return 'b0001;
    1?34 : return 'b0100;
    ?234 : return 'b1000;
    default: return 'b0000;
  endcase
endfunction
