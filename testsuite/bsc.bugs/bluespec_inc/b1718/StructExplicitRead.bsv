typedef struct {
   Bool _read;
} MyStruct;

function Bool doRead(MyStruct s);
   return s._read;
endfunction

