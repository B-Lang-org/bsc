package TypeclassDefaultImport;

import TypeclassDefault::*;

instance Foo#(Int#(8), UInt#(8));
   function foo(x,y);
      return (pack(x)==pack(y));
   endfunction
endinstance


endpackage
