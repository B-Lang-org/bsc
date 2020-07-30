import HasSize::*;

typedef union tagged 
   { struct { a first; MyList#(a) rest; } MyCons;
     void MyNil;
   } MyList#(type a) deriving(Eq);

function Integer myLength(MyList#(a) l);
  case (l) matches
    tagged MyNil: return(0);
    tagged MyCons { rest: .r }: return (1 + myLength(r));
  endcase
endfunction

instance HasSize#(MyList#(a), s) provisos(Literal#(s));
  function size(l);
    return(fromInteger(myLength(l)));
  endfunction
endinstance

