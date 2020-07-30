import Vector :: * ;

(* noinline *)
function int getAt ( Vector#(15,int) v, Bit#(2) idx ) ;
   return v[idx];
endfunction


// (* noinline *)
// function Vector#(5,int) setAt ( Vector#(5,int) v, Bit#(2) idx, int newx ) ;   
//    v[idx] = newx;
//    return v ;
// endfunction


(* noinline *)
function Vector#(15,int) setAt ( Vector#(15,int) v, Bit#(3) idx, int newx ) ;
   let xxx = v ;
   xxx[idx] = newx;
   return xxx ;
endfunction



