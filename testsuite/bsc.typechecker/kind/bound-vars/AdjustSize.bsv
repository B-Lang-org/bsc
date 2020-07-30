function a#(n) adjustSize(a#(m) x)
   provisos(Bits#(a#(n),n), Bits#(a#(m),m),
        BitExtend#(n,s,a), BitExtend#(m,s,a),
        Add#(n,m,s));
   a#(s) y = extend(x);
   return truncate(y);
endfunction

