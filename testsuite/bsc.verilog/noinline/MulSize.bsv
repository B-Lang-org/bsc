typedef Int#(32) DT ;
(* noinline *)
function Tuple3#(DT,DT,DT) test( DT a, DT b, DT c );

   DT x, y, z;
   z = b * a ;
   x = (c * b) + a ;
   y = a + c ;

   return tuple3(x,y,z) ;
endfunction
