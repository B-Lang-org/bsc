package WeakChainRoot;

// A9, residual rooting: the missing proviso is reported as the
// user-written L1#(a), not the L2#(a) its instance reduced to.

typeclass L1#(type a);
  function Bit#(8) l1(a x);
endtypeclass

typeclass L2#(type a);
  function Bit#(8) l2(a x);
endtypeclass

instance L1#(a) provisos (L2#(a));
  function l1(x) = l2(x);
endinstance

function Bit#(8) useL(a x);
  return l1(x);
endfunction
endpackage
