function Bit#(4) caseIntLiteralSigned(Bit#(32) i);
  case (i)
    -1 : return 'b0001;
     0 : return 'b0010;
    +1 : return 'b0100;
    default: return 'b1000;
  endcase
endfunction

function Bit#(4) caseRealLiteralSigned(Real r);
  case (r)
    -1.1 : return 'b0001;
     0.0 : return 'b0010;
    +1.1 : return 'b0100;
    default: return 'b1000;
  endcase
endfunction
