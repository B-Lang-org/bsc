
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        method _write(v) = noAction;

        Bool tmp = True;

        method _read = tmp;
     endinterface
   );
endfunction

