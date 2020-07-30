function Bool f();
   Bool arr[2] = { True, True };
   Bit#(8) ptr = 0;
   // the zeroExtend leads to an unknown size, because the index of
   // selection is already zeroExtended to 32
   Bool res = arr[zeroExtend(ptr)];
   return res;
endfunction

