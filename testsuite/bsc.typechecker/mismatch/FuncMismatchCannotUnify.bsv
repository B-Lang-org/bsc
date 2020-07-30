function Bool f(a x1, a x2) provisos (Eq#(a));
   return (x1 == x2);
endfunction

Integer a = 0;
Bool    b = True;

Bool r = f(a,b);

