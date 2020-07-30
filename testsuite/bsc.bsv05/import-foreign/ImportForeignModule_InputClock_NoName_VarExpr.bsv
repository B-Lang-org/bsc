
import "BVI" MOD =
module mkMyReg (Clock iclk, Reg#(Bool) ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_clock (ICLK) = iclk ;

   method QOUT _read () clocked_by (iclk) ;
   method _write (DIN) enable (EN) clocked_by (iclk) ;

   schedule _read CF _read ;
   schedule _read SB _write ;
   schedule _write SBR _write ;
endmodule

