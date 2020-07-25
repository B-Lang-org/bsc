
import Vector :: * ;
import List :: * ;


//@ \subsubsection{BitUtils}
//@ \index{BitUtils@\te{BitUtils} (package)|textbf}

//@
//@ The Bit Utilities package provides functions for common bit
//@ manipulation.  The advantages of using these functions is that
//@ they have been verified and are known to produce good hardware.
//@
//@   Often several versions of functions are given, where each
//@ version may optimize the hardware along a different axis.


//@ Creates a Vector of size m, listing the indexes of the
//@ lowest m bits set in the bit vector.   Both source and result
//@ sizes (n and m) are compile-time constants.   The resulting vector contains
//@ the indexes of the lowest m bits set, with Vector position 0
//@ containing the index of the lowest element set.
//@ # 5
function Vector#(m,Maybe#(UInt#(idxs_t)))
genLowestIndexes(
           Bit#(n) bitsin )
   provisos( Log#(n, idxs_t), // index size is log of input vector size
             Add#(xxx,1,m) ) ; // output vector size is at least 1 element

   // XXX consider optimizing if m == 1

  Vector#(m,Maybe#(UInt#(idxs_t)))  nullResult = replicate(Invalid) ;
   Integer i ;
   for ( i = valueOf(n) - 1 ; i >= 0; i = i - 1)
      begin
         if ( 1'b1 == bitsin[i] )
            // This is shift with the new element added at the head.
            nullResult = shiftInAt0( nullResult, tagged Valid fromInteger(i) ) ;
      end

   return nullResult ;

endfunction

//@ This function takes a Bit#(n) and returns a Bit#(n) but the resulting bit vector
//@ has at most nSetBits bit which are set.  When more than nSetBits are set within
//@ din, the bits with the lowest indexed are copied, while the higher indexed ones
//@ are zeroed.
//@  The argument nSetBits can be changed during runtime.  The resulting hardware
//@ contains n comparators and n conditional incrementors.
//@ # 7
function Bit#(n)
copyLowestNBits(
                UInt#(idxs_t) nSetBits,
                Bit#(n) din )
   provisos( Add#(xxx, 1, n ),    // n is at least 1
            Add#(xxy,1,idxs_t)    // idx_st is at
) ;

   function Tuple2#( UInt#(idxs_t), Bit#(1) ) mapa_func( UInt#(idxs_t) cntin,  Bit#(1) bitin ) ;
      UInt#(idxs_t)  sum = cntin + unpack( zeroExtend( bitin ) ) ;
      Bit#(1)      bitout = bitin & ( pack (cntin <  nSetBits  )) ;
      return tuple2( sum, bitout ) ;
   endfunction

   Vector#(n, Bit#(1)) vin  = unpack( din ) ;

   let tres = mapAccumL( mapa_func, 0 , vin ) ;
   Vector#(n, Bit#(1)) vout = tpl_2( tres ) ;
   Bit#(n)  res = pack( vout ) ;
   return res ;

endfunction


//@ This function takes a Bit#(n) and returns a Bit#(n) but the resulting bit vector
//@ has at most nSetBits bit which are set.  When more than nSetBits are set within
//@ din, the bits with the lowest indexed are copied, while the higher indexed ones
//@ are zeroed.
//@  The argument nSetBits is a compile-time constant.
//@ The resulting hardware contains nSetBits decrementors in series
//@ # 4
function Bit#(n)
copyLowestNBits_static(
            Integer nSetBits,
            Bit#(n) din )  ;

   Bit#(n) newd = din ;
   Bit#(n) mask =  0;
   Integer i ;
   for( i = 0; i < nSetBits; i = i + 1)
      begin
         Bit#(n) d  = newd ;
         Bit#(n) d1 = d - 1;

         newd = d & d1 ;
         mask = mask | (d ^ d1) ;
      end

   return din & mask ;

endfunction


//@ Count Leading Zeros
//@ Returns the count of number of leading zeros in a bit vector.   Leading zeros are
//@ counted from the highest index (MSB) of din.
//@ # 5
function UInt#(idxs_t)
countLeadingZeros (
                   Bit#(n) din)
   provisos(Log#(n, k),
            Add#(k, 1, idxs_t));   // idxs_t = log(n) + 1

   // XXX TODO need to cleanup error message bar and foo.

   function UInt#(m) nzPassLeft( UInt#(m) a, UInt#(m) b);
      return((a == 0) ? b : a);
   endfunction

   function List#(UInt#(m)) clz_list_reduce(Integer n, List#(UInt#(m)) results);
      return
      ((n == 0) ?
       ((List::length(results) == 1) ? results : error("bar"))  :
       clz_list_reduce(n - 1, List::mapPairs(nzPassLeft, error("foo"), results)));
   endfunction : clz_list_reduce

   function UInt#(m) clz_reduce(Bit#(n) data)
      provisos(Log#(n, k), Add#(k, 1, m));

      Integer n = valueOf(n);
      function UInt#(m) seedsize(Integer i) ;
         return     ((i == n) ||
                     (1'b1 == data[fromInteger(n - (i + 1))]) ? fromInteger(i) : 0);
      endfunction

      List#(UInt#(m)) seeds = List::map(seedsize, List::upto(1, valueOf(n)));

      return(List::head(clz_list_reduce(valueOf(k), seeds)));

   endfunction : clz_reduce

   // the
   return ((1'b1 == din [ fromInteger(valueOf(n) - 1) ] ) ? 0 : clz_reduce(din));
endfunction
