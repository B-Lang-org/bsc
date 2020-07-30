
function Bool topFn (Reg#(Bool) x, Reg#(Bool) y);
   begin
      function f ( Reg#(Bool) a, Reg#(Bool) b );
         return (a._read && b._read) ;
      endfunction
      return f(x,y);
   end
endfunction

