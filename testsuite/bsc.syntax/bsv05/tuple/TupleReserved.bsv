`ifdef TYPE_NAME
typedef Bool `NAME;
`elsif PARAMETER_NAME
function Bool f(Bool `NAME) = True;
`elsif FIELD_NAME
typedef struct { Bool `NAME; } S;
`elsif METHOD_NAME
interface I;
   method Bool `NAME ();
endinterface
`elsif LOCAL_NAME
function Bool f();
   Bool `NAME = True;
   return True;
endfunction
`elsif PATTERN_NAME
function Bool f();
   match {.`NAME, .b} = tuple(True, False);
   return b;
endfunction
`elsif QUALIFIED_TYPE
typedef TupleReserved::Tuple#(Bool) T;
`elsif EMPTY_OTHER_TYPE
typedef Bit#() T;
`elsif BARE_TYPE
typedef Tuple T;
`elsif BARE_VALUE
function Bool f();
   let g = tuple;
   return True;
endfunction
`else
function Bool `NAME (Bool b) = !b;
`endif
