typedef struct {
   Bit#(isize) i;
   Bit#(fsize) f;
} MyFixedPoint#(numeric type isize, numeric type fsize)
deriving (Eq);

instance Literal#( MyFixedPoint#(i,f) );
   function inLiteralRange(i) = error ("not defined");
   function fromInteger(i)    = error ("not defined");
endinstance

instance Arith#( MyFixedPoint#(i,f) )
   provisos( Add#(i,f,b)
            ,Add#(TAdd#(i,i), TAdd#(f,f), TAdd#(b,b))
           );

   function \+ (in1, in2)   = error ("not defined");
   function \- (in1, in2)   = error ("not defined");
   function \* (in1, in2)   = error ("not defined");
   function \/ (in1, in2)   = error ("not defined");
   function \% (in1, in2)   = error ("not defined");
   function \** (in1, in2)  = error ("not defined");
   function negate (in)     = error ("not defined");
   function abs (in)        = error ("not defined");
   function signum (in)     = error ("not defined");
   function exp_e (in)      = error ("not defined");
   function log (in)        = error ("not defined");
   function log2 (in)       = error ("not defined");
   function log10 (in)      = error ("not defined");
   function logb (in1, in2) = error ("not defined");
endinstance

function MyFixedPoint#(ri,rf)
   my_mult(MyFixedPoint#(ai,af) x,
           MyFixedPoint#(bi,bf) y)
   provisos( Add#(ai,bi,ri)
            ,Add#(af,bf,rf)
            ,Add#(ri,rf,rb)
           );
   return gen;
endfunction

function t gen()
   provisos ( Arith#(t) );

   return ?;
endfunction

