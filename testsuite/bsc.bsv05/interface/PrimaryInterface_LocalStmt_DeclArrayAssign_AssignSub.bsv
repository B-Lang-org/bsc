
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        Bool tmp[3] = { True, True, True };
        tmp[0] = False;

        method _read = tmp[0];
        method _write(v) = noAction;
     endinterface
   );
endfunction

