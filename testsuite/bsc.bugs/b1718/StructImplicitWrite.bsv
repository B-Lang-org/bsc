typedef struct {
   function Action f(Bool x)  _write;
} MyStruct;

function Action doWrite(MyStruct s, Bool b);
 action
   s <= b;
 endaction
endfunction

