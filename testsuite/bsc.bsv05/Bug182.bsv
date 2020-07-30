function Bit#(n) f9 (Bit#(3) s, Bit#(n) x) ;
      Bit#(n) result;
      case (s) 
        0 :  begin result = x; end
        default :  begin result = x; end
      endcase
      f9 = result;
endfunction
