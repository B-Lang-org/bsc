package ModuleCollect;
/*
export ModuleCollect;
export addToCollection;
export mapCollection;
export getCollection;
export IWithCollection(..);
export exposeCollection;
*/
import ModuleContext::*;
import UnitAppendList::*;
import HList::*;

typedef ModuleContext#(HList1#(UAList#(a))) ModuleCollect#(type a);

module [mc] addToCollection#(a r)(Empty)
   provisos (IsModule#(mc, _1), Context#(mc, UAList#(a)));
   UAList#(a) s <- getContext();
   putContext(tagged Append tuple2(s, tagged One r));
endmodule

module [mc] mapCollection#(function a f(a x), mc#(i) m)(i)
   provisos (IsModule#(mc, _1), Context#(mc, UAList#(a)));
   let i <- m;
   UAList#(a) c <- getContext();
   putContext(uaMap(f, c));
   return i;
endmodule


module [Module] getCollection#(ModuleCollect#(a, i) x1)(Tuple2#(i, List#(a)));
   let {c,i} <- runWithCompleteContext(hList1(NoItems), x1);
   return (tuple2(i, flatten(hHead(c))));
endmodule

interface IWithCollection #(type a, type i);
    method i device();
    method List#(a) collection();
endinterface: IWithCollection

module [Module] exposeCollection#(ModuleCollect#(a, i) _m)(IWithCollection#(a, i));
  let {_d,_xs} <- getCollection(_m);
  method device = _d;
  method collection = _xs;
endmodule: exposeCollection

endpackage
