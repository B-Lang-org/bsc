typedef struct {
   function Action f(Bool x)  _write;
} MyStruct;

function Action doWrite(MyStruct s, Bool b);
   return s._write(b);
endfunction

