
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        let tmp = True;

        method _read = tmp;
        method _write(v) = noAction;
     endinterface
   );
endfunction

