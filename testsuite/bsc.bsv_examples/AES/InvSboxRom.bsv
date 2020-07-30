package InvSboxRom;

import RegFile::*;

interface InvSboxRom;
   method Bit#(8) read( Bit#(8) addr );
endinterface

(* synthesize *)
module mkInvSboxRom ( InvSboxRom );
   RegFile#(Bit#(8),Bit#(8)) invsbox   <- mkRegFileLoad("invsbox.table", 0, 255);
   method Bit#(8) read( Bit#(8) addr );   
      return invsbox.sub( addr );
   endmethod
endmodule
endpackage

   
