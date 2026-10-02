package TDBase;
import TCBase::*;

// A class whose instance CONTEXT demands TC evidence: dictionaries
// for TD embed a TC dictionary as a sub-dictionary, so two TD
// dictionaries can share the same instance but differ in the
// evidence of their sub-dictionary.
typeclass TD#(type t);
   function Bit#(8) dtag(t x);
endtypeclass

instance TD#(t) provisos (TC#(t));
   function dtag(x) = tag(x) + 8'd10;
endinstance

endpackage
