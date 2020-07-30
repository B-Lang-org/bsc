import Vector :: *;

typedef Bit#(8) Byte;

function Bit#(32) addUp (Vector#(n, Byte) vv,
             UInt#(TLog#(n)) lln);

   function Vector#(nn, Byte) trim (Vector#(nn, Byte) v,
                   UInt#(TLog#(nn)) ln);
      UInt#(TAdd#(TLog#(nn),1)) eln = extend(ln);
      Integer ms = valueof(nn);
      function Byte f(Byte b, Integer i) =
     (fromInteger(ms -i) > eln ? 0 : b);
      return zipWith(f, v, genVector);
   endfunction

   function Vector#(TDiv#(nn,2), Bit#(16)) pairUp (Vector#(nn, Byte) v);
      function Bit#(16) f2 (Byte x, Byte y) = {x,y};
      function Bit#(16) f1 (Byte x) = {x,0};
      return mapPairs(f2, f1, reverse(v));
   endfunction

   function Vector#(TDiv#(nn,2), Bit#(32)) stage (Vector#(nn, Bit#(m)) v)
      provisos (Add#(m, _1, 32));

      function Bit#(32) f2 (Bit#(m) x, Bit#(m) y) = extend(x) + extend(y);
      function Bit#(32) f1 (Bit#(m) x) = extend(x);
      return mapPairs(f2, f1, v);
   endfunction

   let x = head(stage(
            stage(
            stage(
            stage(
            stage(
            stage(
            stage(
            stage(
            stage(
            stage(
            stage(
            stage(
        stage(pairUp(trim(vv,lln))) )))))))))))));
   return x;
endfunction