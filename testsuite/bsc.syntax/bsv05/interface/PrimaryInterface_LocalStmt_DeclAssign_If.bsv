
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        Bool tmp = True;
        if (x)
	   tmp = False;

        method _read = tmp;
        method _write(v) = noAction;
     endinterface
   );
endfunction

