
// XXX it'd be nice if you could leave off the string
(* deprecate = "" *)
function Bool myFn (Bool x);
   return !x;
endfunction

(* deprecate = "Replaced by mkNewFoo." *)
module mkFoo();
endmodule

(* deprecate = "" *)
import "BVI" FOO =
module mkImp(Reg#(Bool));
   default_clock clk();
   default_reset rst();

   method Q_OUT _read();
   method _write(D_IN) enable(EN);
   schedule _read CF _read;
   schedule _read SB _write;
   schedule _write SBR _write;
endmodule

