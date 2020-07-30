//Parser bug prevents this code from working
//Bool x[2] = {True, True};
//Bool y = x[True];

function Bool f();
   Bool x[2] = {True, True};
   Bool y = x[True];
   return y;
endfunction

