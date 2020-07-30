
function Bool topFn (Bool x, Bool y);
   begin
      function f ( int a, int b );
         return (a && b) ;
      endfunction
      return f(x,y);
   end
endfunction

