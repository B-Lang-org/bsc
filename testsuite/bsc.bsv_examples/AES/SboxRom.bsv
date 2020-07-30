import RegFile::*;

interface SboxRom;
   method Bit#(8) read( Bit#(8) addr );
endinterface

(* synthesize *)
module mkSboxRom ( SboxRom );
   RegFile#(Bit#(8),Bit#(8)) sbox   <- mkRegFileLoad("sbox.table", 0, 255);

   method Bit#(8) read( Bit#(8) addr ) = sbox.sub( addr );

endmodule

   
