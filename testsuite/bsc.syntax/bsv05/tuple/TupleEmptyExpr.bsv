// Empty tuple types and values are the existing unit type and value

function void f();
   return tuple();
endfunction

function Tuple#() toTuple(void x) = x;
function void fromTuple(Tuple#() x) = x;
function Bit#(0) packUnit() = pack(tuple());
