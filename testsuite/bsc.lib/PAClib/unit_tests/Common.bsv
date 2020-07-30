import Vector::*;


typedef  4             MK_t;
typedef  TLog #(MK_t)  LogMK_t;

typedef Vector #(MK_t, int)  Vec_int;

// ================================================================
// General utilities


function Action display_Vec_int (String preString,
                                 String preEachString,
                                 Vector #(n, int) vx,
                                 Bool newline);
   action
      $write ("%s", preString);
      for (Integer j = 0; j < valueof (n); j = j + 1) $write ("%s%0d", preEachString, vx [j]);
      if (newline) $display();
   endaction
endfunction

// ----------------------------------------------------------------
// Cycle count
function ActionValue #(Bit #(64)) cyclenum ();
   actionvalue
      Bit #(64) timescale = 10;
      let t <- $time ;
      t = t +   timescale/2 ;   // hack to get bluesim and verilog at the same time
      return (t / timescale);
   endactionvalue
endfunction

// ----------------------------------------------------------------
// Increment by n
function  t  f_incr_by  (Integer n, t x)
        provisos (Arith #(t));
   return (fromInteger (n) + x);
endfunction

// ----------------------------------------------------------------
// Print vector of ints
function Action display_Vec_xs (String preString, Vec_int vi);
   action
     display_Vec_int (preString, " ", vi, True);
   endaction
endfunction

// ----------------------------------------------------------------
// Print vector of (ints,index) tuples
function Action display_Vec_xjs (String preString, Vector #(m, Tuple2 #(int, UInt #(logmk))) v_x_j);
   action
      $write (preString);
      for (Integer k = 0; k < valueof (m); k = k + 1) begin
         match { .x, .j } = v_x_j [k];
         $write (" (%0d, %0d)", x, j);
      end
      $write ("\n");
   endaction
endfunction
