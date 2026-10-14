package UnitAppendList;

import Foldable::*;
import Traversable::*;

typedef union tagged {
    void NoItems;
    a One;
    Tuple2#(UAList#(a),UAList#(a)) Append;
} UAList#(type a);

instance DefaultValue#(UAList#(a));
   defaultValue = NoItems;
endinstance


function List#(a) flatten0(UAList#(a) c, List#(a) xs);
   case (c) matches
      tagged NoItems:          return xs;
      tagged One .x:           return Cons (x, xs);
      tagged Append {.c1,.c2}: return (flatten0(c1, flatten0(c2, xs)));
   endcase
endfunction: flatten0

function List#(a) flatten(UAList#(a) c) = flatten0(c, Nil);


// Append two lists, treating NoItems as the identity so the result never
// contains a redundant empty branch.
function UAList#(a) uaAppend(UAList#(a) c1, UAList#(a) c2) =
   c1 matches tagged NoItems ? c2 :
   c2 matches tagged NoItems ? c1 :
   tagged Append tuple2(c1, c2);


function UAList#(b) uaMap(function b f(a x), UAList#(a) c);
   case (c) matches
      tagged NoItems:          return tagged NoItems;
      tagged One .x:           return tagged One (f(x));
      tagged Append {.c1,.c2}: return uaAppend(uaMap(f, c1), uaMap(f, c2));
   endcase
endfunction: uaMap

module uaMapM#(function module#(b) f(a x), UAList#(a) c)(UAList#(b));
   case (c) matches
      tagged NoItems:
	 return tagged NoItems;
      tagged One .x:
	 begin
	    let y <- f(x);
	    return tagged One y;
	 end
      tagged Append {.c1,.c2}:
	 begin
	    let r1 <- uaMapM(f, c1);
	    let r2 <- uaMapM(f, c2);
	    return uaAppend(r1, r2);
	 end
   endcase
endmodule: uaMapM


instance Functor#(UAList);
   function fmap = uaMap;
endinstance

instance Foldable#(UAList);
   function b foldr(function b f(a x, b z), b z, UAList#(a) c);
      case (c) matches
         tagged NoItems:          return z;
         tagged One .x:           return f(x, z);
         tagged Append {.c1,.c2}: return foldr(f, foldr(f, z, c2), c1);
      endcase
   endfunction
   function toList = flatten;
endinstance

instance Traversable#(UAList);
   function f#(UAList#(b)) traverse(function f#(b) func(a x), UAList#(a) c)
      provisos (Applicative#(f));
      case (c) matches
         tagged NoItems:  return \pure (tagged NoItems);
         tagged One .x:   return fmap(One, func(x));
         tagged Append {.c1,.c2}:
            return liftA2(uaAppend, traverse(func, c1), traverse(func, c2));
      endcase
   endfunction
endinstance

endpackage
