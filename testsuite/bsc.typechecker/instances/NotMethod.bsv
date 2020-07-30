import Displayable::*;

instance Displayable#(String);
   function Action write(String a);
     $display(a);
   endfunction
endinstance
