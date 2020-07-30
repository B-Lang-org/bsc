
import "BVI" VMod =
module mkMod (Reg#(Bool));
   
   method _write (D_IN) enable (EN);
   method Q_OUT _read;

   schedule _write SBR _write;
   schedule _read CF _read;   
   // duplicates
   schedule _read SB _write;
   schedule _write CF _read;  // check that the swapped order is detected!
endmodule

