// send data out to files for read by screen!

import "BDPI" function Action sendToScreen ( Bit#(8) x );
                 
interface Screen;
   method Action send( Bit#(8) x );
endinterface

(* synthesize *)
module mkScreen ( Screen );
   method Action send( Bit#(8) x ) = sendToScreen( x );
endmodule
