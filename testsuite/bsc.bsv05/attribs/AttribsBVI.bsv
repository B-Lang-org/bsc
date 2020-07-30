
import "BVI" VMod =
module mkMod (Reg#(Bool));

   (* always_enabled *)
   method _write (D_IN) enable (EN);
   method Q_OUT _read;

   schedule _write SBR _write;
   schedule _read CF _read;
   schedule _read SB _write;
endmodule

