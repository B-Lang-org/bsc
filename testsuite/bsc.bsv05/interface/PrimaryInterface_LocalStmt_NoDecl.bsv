
function Reg#(Bool) mkFn(Bool x);
  Bool tmp = True;
  return (
     interface Reg;
        if (x)
	   tmp = False;
        method _read = tmp;
        method _write(v) = noAction;
     endinterface
   );
endfunction

