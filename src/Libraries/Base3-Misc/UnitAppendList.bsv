package UnitAppendList;

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


function UAList#(b) uaMap(function b f(a x), UAList#(a) c);
   case (c) matches
      tagged NoItems:          return tagged NoItems;
      tagged One .x:           return tagged One (f(x));
      tagged Append {.c1,.c2}:
	 begin
	    let r1 = uaMap(f, c1);
	    let r2 = uaMap(f, c2);
	    return (r1 matches tagged NoItems ? r2 :
		    r2 matches tagged NoItems ? r1 :
		    tagged Append tuple2(r1, r2));
	 end
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
	    return (r1 matches tagged NoItems ? r2 :
		    r2 matches tagged NoItems ? r1 :
		    tagged Append tuple2(r1, r2));
	 end
   endcase
endmodule: uaMapM

endpackage
