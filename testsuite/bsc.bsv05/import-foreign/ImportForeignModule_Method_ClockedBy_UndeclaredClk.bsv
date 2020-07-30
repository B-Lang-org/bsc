
import "BVI" MOD =
module mkMyReg (Reg#(Bool) ifc) ;

   method QOUT _read () clocked_by (foo) ;
   method _write (DIN) enable (EN) ;

   schedule _read CF _read ;
   schedule _read SB _write ;
   schedule _write SBR _write ;
endmodule

