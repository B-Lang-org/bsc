typedef 32 SiteIds;
typedef struct { Bit#(TLog#(SiteIds)) v;} SiteId deriving (Eq, Bits, Arith, Literal);

//instance PrimIndex#(SiteId, TLog#(SiteIds));
instance PrimIndex#(SiteId, SiteIds);
   function isStaticIndex(x)  = isStaticIndex(x.v);
   function toStaticIndex(x)  = toStaticIndex(x.v);
   function toDynamicIndex(x) = toDynamicIndex(x.v);
endinstance

