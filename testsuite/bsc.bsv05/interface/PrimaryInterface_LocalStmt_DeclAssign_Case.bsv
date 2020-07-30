
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        Bool tmp = True;
        case (x)
	   True : tmp = False;
	   False : tmp = True;
	endcase

        method _read = tmp;
        method _write(v) = noAction;
     endinterface
   );
endfunction

