
import "BVI" MOD =
module mkMyReg (Reset irst, Reg#(Bool) ifc) ;
   no_reset ;

   input_reset (IRST) = irst ;

   method QOUT _read () reset_by (irst) ;
   method _write (DIN) enable (EN) reset_by (irst) ;

   schedule _read CF _read ;
   schedule _read SB _write ;
   schedule _write SBR _write ;
endmodule

