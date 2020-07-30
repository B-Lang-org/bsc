
function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        function Bool fn();
            return True;
        endfunction

        method _read = fn;
        method _write(v) = noAction;
     endinterface
   );
endfunction

