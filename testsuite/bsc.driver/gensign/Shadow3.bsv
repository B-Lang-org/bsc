
import Basic::*;

export Basic::*;
export myFn1;
export S(..);

function Bool myFn1(Integer x);
  return (x > 2);
endfunction

typedef enum { A, B } S;

