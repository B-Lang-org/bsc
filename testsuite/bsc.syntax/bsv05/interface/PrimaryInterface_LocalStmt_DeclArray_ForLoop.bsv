
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        Bool tmp[3];
        for (Integer i = 0; i < 3; i = i + 1) tmp[i] = True;

        method _read = tmp[0] && tmp[1] && tmp[2];
        method _write(v) = noAction;
     endinterface
   );
endfunction

