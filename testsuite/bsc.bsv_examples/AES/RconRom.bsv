package RconRom;

import RegFile::*;

interface RconRom;
   method Bit#(32) read( Bit#(4) addr );
endinterface

(* synthesize *)
module mkRconRom ( RconRom );
   RegFile#(Bit#(4),Bit#(32)) rcon    <- mkRegFileLoad("rcon.table", 0, 9);   

   method Bit#(32) read( Bit#(4) addr );   
      return rcon.sub( addr );
   endmethod
endmodule
endpackage

   
