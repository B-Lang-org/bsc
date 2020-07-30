// NOTE  this file is a template which requires the following tick-defines
//`define is 10
//`define fs 10
//`define full sysFromReal_10_10

import Real :: *;
import FixedPoint :: *;
import List :: *;

(* synthesize *)
module `full ();
   
   rule doit ;
      showfp(pi);
      showfp(1.0);
      showfp(1.0e2);
      showfp(1.0e-4);
      showfp(1.0/128);
      showfp(-1.0);
      showfp(-4.0);
      showfp(4e23);
      showfp(-4e23);
      showfp(1.0/3.0);
      showfp(-1.0/3.0);
      showfp(1 * 2**5);
      showfp(0 - 1 * 2**5);
      
      showfp(1 * 2**-5);
      showfp(0 - 1 * 2**-5);
      
      showfp(1 * 2**-5);
      showfp(-1 * 2**-4);
      showfp((-1) * 2**-4);
      showfp(1*2**-1034);       // denormalized
      showfp((-1)*2**-1035);       // denormalized

      showfp((-1)* (2**-1011));       // denormalized
      showfp((-1)* (2**-1034));       // denormalized
      


      $finish(0);
   endrule
   
endmodule


function Action showfp (Real n );
   return
   (action
       $write ( "Converting %s  = ", realToString(n) );
       FixedPoint#(`is,`fs) f = fromReal(n);
       fxptWrite( 10, f ); $display ( "" );
       $display( "%b.%b", fxptGetInt(f), fxptGetFrac(f));
    endaction);
endfunction
