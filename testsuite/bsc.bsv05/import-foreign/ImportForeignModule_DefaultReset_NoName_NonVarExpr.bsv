
import "BVI" MOD =
module mkMyReg (Reg#(Bool) ifc) ;

   default_reset (RST) <- exposeCurrentReset ;

   method QOUT _read () ;
   method _write (DIN) enable (EN) ;

   schedule _read CF _read ;
   schedule _read SB _write ;
   schedule _write SBR _write ;
endmodule

