import Vector :: * ;

// Odd even sort
function Vector#(n, a ) sortoe (function Bool lt (a l, a r ),
                                Vector#(n,a) vin ) provisos(Bits#(a,sa), Mul#(n,sa,q));
   
   // 1 step in the odd/even sort
   function Bit#(q) oesortstep (Vector#(n,a) vx);
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
      return pack(odd);
   endfunction
                                   
   Integer i;
   Bit#(q) ret = pack(vin);
   for (i=0; i < valueOf(n); i = i + 2)
      begin
         ret = oesortstep(unpack(ret));
      end
   return unpack(ret);
endfunction
   
function Vector#(sz, Bit#(8)) byteEnableSort (Vector#(sz, Bit#(8)) din,
                                              Vector#(sz, Bool)  be );
   
   Vector#( sz, Tuple2#(Bool, Bit#(8))) z = zip ( be, din);

   function Bool lt ( Tuple2#(Bool, Bit#(8)) l, Tuple2#(Bool, Bit#(8)) r );
      return (! tpl_1(l)  && tpl_1(r));
   endfunction

   let f = sortoe( lt, z );
   return map (tpl_2, f);

endfunction    

(* noinline *)
function Vector#(2, Bit#(8)) beSort_2(Vector#(2, Bit#(8)) din, Vector#(2,Bool) be) = byteEnableSort(din, be);
   
(* noinline *)
function Vector#(4, Bit#(8)) beSort_4(Vector#(4, Bit#(8)) din, Vector#(4,Bool) be) = byteEnableSort(din, be);
   
(* noinline *)
function Vector#(8, Bit#(8)) beSort_8(Vector#(8, Bit#(8)) din, Vector#(8,Bool) be) = byteEnableSort(din, be);
   
(* noinline *)
function Vector#(16, Bit#(8)) beSort_16(Vector#(16, Bit#(8)) din, Vector#(16,Bool) be) = byteEnableSort(din, be);
   
(* noinline *)
function Vector#(32, Bit#(8)) beSort_32(Vector#(32, Bit#(8)) din, Vector#(32,Bool) be) = byteEnableSort(din, be);
