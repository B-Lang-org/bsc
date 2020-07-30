
typedef struct {
    Bool f1;
    Bool f2;
} S deriving (Eq, Bits);

function Reg#(Bool) mkFn(Bool x);
  return (
     interface Reg;
        S tmp;
        tmp.f1 = False;
	tmp.f2 = True;

        method _read = tmp.f1;
        method _write(v) = noAction;
     endinterface
   );
endfunction

