package HList;

typedef struct {} HNil deriving (Eq);
HNil hNil = HNil{};

typedef struct {
   e hd;
   l tl;
		} HCons#(type e, type l) deriving (Eq);

function HCons#(e,l) hCons(e x, l xs) = HCons {hd: x, tl: xs};

typeclass HList#(type l); endtypeclass

instance HList#(HNil); endinstance
instance HList#(HCons#(e,l)) provisos (HList#(l)) ; endinstance


//-----------------------------------------------------------------------------

// Basic list functions

typeclass HHead#(type l, type h)
   dependencies (l determines h);
   function h hHead(l x);
endtypeclass

instance  HHead#(HCons#(e, l), e);
   function hHead(xs) = xs.hd;
endinstance

typeclass HTail#(type l, type lt)
   dependencies (l determines lt);
   function lt hTail(l xs);
endtypeclass

instance HTail#(HCons#(e, l), l);
   function hTail(xs) = xs.tl;
endinstance

typeclass HLength#(type l, numeric type n)
   dependencies (l determines n);
endtypeclass

instance HLength#(HNil, 0); endinstance

instance HLength#(HCons#(e, l), nPlus1)
   provisos (HLength#(l, n), Add#(n,1,nPlus1));
endinstance

function Integer hLength(hL xs)
   provisos (HLength#(hL, n));
   return valueof(n);
endfunction

//-----------------------------------------------------------------------------

// Appending HLists


typeclass HAppend#(type l, type l1, type l2)
   dependencies ((l, l1) determines l2);
   function l2 hAppend(l xs, l1 ys);
endtypeclass


instance HAppend#(HNil, l, l);
   function hAppend(nl, xs) = xs;
endinstance

instance HAppend#(HCons#(e, l), l1, HCons#(e, l2))
   provisos (HList#(l), HAppend#(l, l1, l2));
   function hAppend(xs, ys) = hCons(hHead(xs), hAppend(hTail(xs), ys));
endinstance

//-----------------------------------------------------------------------------

// A typeclass for the inverse of HAppend

typeclass HSplit#(type l, type l1, type l2);
   function Tuple2#(l1,l2) hSplit(l xs);
endtypeclass

instance HSplit#(HNil, HNil, HNil);
   function hSplit(xs) = tuple2(hNil,hNil);
endinstance

instance HSplit#(l, HNil, l);
   function hSplit(xs) = tuple2(hNil,xs);
endinstance

instance HSplit#(HCons#(hd,tl), HCons#(hd,l3), l2)
   provisos (HSplit#(tl,l3,l2));
   function hSplit(xs);
      tl tlv = hTail(xs);
      Tuple2#(l3,l2) spv = hSplit(tlv);
      match {.ys, .zs} = spv;
      return tuple2(hCons(hHead(xs), ys), zs);
   endfunction
endinstance

//-----------------------------------------------------------------------------

// A typeclass for finding and replacing an element of an HList

typeclass Gettable#(type c1, type c2);
   function c2 getIt(c1 x);
   function c1 putIt(c1 x, c2 y);
endtypeclass

instance Gettable#(HCons#(t1, t2), t1);
   function getIt(x)   = hHead(x);
   function putIt(x,y) = hCons(y, hTail(x));
endinstance

instance Gettable#(HCons#(t1, t2), t3)
   provisos (Gettable#(t2, t3));

   function getIt(x)   = getIt(hTail(x));
   function putIt(x,y) = hCons(hHead(x), putIt(hTail(x),y));
endinstance

//-----------------------------------------------------------------------------

// Small lists

typedef HCons#(t, HNil)                                      HList1#(type t);
typedef HCons#(t1, HCons#(t2, HNil))                         HList2#(type t1, type t2);
typedef HCons#(t1, HCons#(t2, HCons#(t3, HNil)))             HList3#(type t1, type t2, type t3);
typedef HCons#(t1, HCons#(t2, HCons#(t3, HCons#(t4, HNil)))) HList4#(type t1, type t2, type t3, type t4);

typedef HCons#(t1, HCons#(t2, HCons#(t3, HCons#(t4,
   HCons#(t5, HNil)))))
              HList5#(type t1, type t2, type t3, type t4, type t5);

typedef HCons#(t1, HCons#(t2, HCons#(t3, HCons#(t4,
   HCons#(t5, HCons#(t6, HNil))))))
              HList6#(type t1, type t2, type t3, type t4, type t5, type t6);

typedef HCons#(t1, HCons#(t2, HCons#(t3, HCons#(t4,
   HCons#(t5, HCons#(t6, HCons#(t7, HNil)))))))
              HList7#(type t1, type t2, type t3, type t4, type t5, type t6, type t7);

typedef HCons#(t1, HCons#(t2, HCons#(t3, HCons#(t4,
   HCons#(t5, HCons#(t6, HCons#(t7, HCons#(t8, HNil))))))))
              HList8#(type t1, type t2, type t3, type t4, type t5, type t6, type t7, type t8);

function HList1#(t1)             hList1(t1 x1)                      = hCons(x1, hNil);
function HList2#(t1, t2)         hList2(t1 x1, t2 x2)               = hCons(x1, hCons(x2, hNil));
function HList3#(t1, t2, t3)     hList3(t1 x1, t2 x2, t3 x3)        = hCons(x1, hCons(x2, hCons(x3, hNil)));
function HList4#(t1, t2, t3, t4) hList4(t1 x1, t2 x2, t3 x3, t4 x4)
      = hCons(x1, hCons(x2, hCons(x3, hCons(x4, hNil))));

function HList5#(t1, t2, t3, t4, t5)
   hList5(t1 x1, t2 x2, t3 x3, t4 x4, t5 x5)
      = hCons(x1, hCons(x2, hCons(x3, hCons(x4, hCons(x5, hNil)))));

function HList6#(t1, t2, t3, t4, t5, t6)
   hList6(t1 x1, t2 x2, t3 x3, t4 x4, t5 x5, t6 x6)
      = hCons(x1, hCons(x2, hCons(x3, hCons(x4, hCons(x5, hCons(x6, hNil))))));

function HList7#(t1, t2, t3, t4, t5, t6, t7)
   hList7(t1 x1, t2 x2, t3 x3, t4 x4, t5 x5, t6 x6, t7 x7)
      = hCons(x1, hCons(x2, hCons(x3, hCons(x4, hCons(x5, hCons(x6, hCons(x7, hNil)))))));

function HList8#(t1, t2, t3, t4, t5, t6, t7, t8)
   hList8(t1 x1, t2 x2, t3 x3, t4 x4, t5 x5, t6 x6, t7 x7, t8 x8)
      = hCons(x1, hCons(x2, hCons(x3, hCons(x4, hCons(x5, hCons(x6, hCons(x7, hCons(x8, hNil))))))));

endpackage
