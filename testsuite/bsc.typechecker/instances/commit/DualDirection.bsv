// Test that an unreachable same-class given with contradictory concrete
// arguments does not block discharge through a diagonal instance.
typeclass CC#(numeric type a, numeric type b);
   function Bit#(b) ccv(Bit#(a) x);
endtypeclass

instance CC#(w, w)
   provisos (Mul#(TDiv#(w,8), 8,
                  TAdd#(TSub#(TMul#(TDiv#(w,8), 8), w), w)));
   function ccv(x) = x;
endinstance

function Bit#(r) f(Bit#(r) x) provisos (CC#(4,8));
   return ccv(x);
endfunction
