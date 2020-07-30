import RegFile::*;

interface RconRom;
   method Bit#(32) read( Bit#(4) addr );
endinterface

(* synthesize, always_ready, always_enabled *)
module mkRconRom ( RconRom );

   method Bit#(32) read( Bit#(4) addr ) =
      case (addr)
         0: return 32'h01000000;
         1: return 32'h02000000;
         2: return 32'h04000000;
         3: return 32'h08000000;
         4: return 32'h10000000;
         5: return 32'h20000000;
         6: return 32'h40000000;
         7: return 32'h80000000;
         8: return 32'h1b000000;
         9: return 32'h36000000;
         default: return ?;
      endcase;
      
endmodule

   
