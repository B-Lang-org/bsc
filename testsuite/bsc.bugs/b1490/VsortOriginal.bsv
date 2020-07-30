typedef 16 Sz;


import Vector :: * ;

// Odd even sort
function Vector#(n, a ) sortoe (function Bool lt (a l, a r ),
                                Vector#(n,a) vin );
   
   // 1 step in the odd/even sort
   function Vector#(n, a) oesortstep (Vector#(n,a) vx );
      Integer j;
      Vector#(n, a) evn = vx;
      for(j = 1; j < valueOf(n); j = j + 2)
         begin
            if (lt (vx[j-1], vx[j]))
               begin
                  evn[j-1] = vx[j];
                  evn[j]   = vx[j-1];
               end
         end
      Vector#(n, a) odd = evn;
      for(j = 2; j < valueOf(n); j = j + 2)
         begin
            if (lt (evn[j-1], evn[j]))
               begin
                  odd[j-1] = evn[j];
                  odd[j] = evn[j-1];
               end
         end
      return odd;
   endfunction
                                   
   Integer i;
   Vector#(n, a) ret = vin ;
   for (i=0; i < valueOf(n); i = i + 2)
      begin
         ret = oesortstep(ret);
      end
   return ret;
endfunction
   

   


   
(*noinline*)
function Vector#(Sz, Bit#(8)) byteEnableSort (Vector#(Sz, Bit#(8)) din,
                                              Vector#(Sz, Bool)  be );
   
   Vector#( Sz, Tuple2#(Bool, Bit#(8))) z = zip ( be, din);

   function Bool lt ( Tuple2#(Bool, Bit#(8)) l, Tuple2#(Bool, Bit#(8)) r );
      return (! tpl_1(l)  && tpl_1(r));
   endfunction

   let f = sortoe( lt, z );
   return map (tpl_2, f);

endfunction    
      
