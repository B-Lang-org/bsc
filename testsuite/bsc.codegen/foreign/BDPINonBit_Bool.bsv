import "BDPI" function Bool my_and (Bool x, Bool y);
import "BDPI" function Bool my_xor (Bool x, Bool y);

(* synthesize *)
module mkBDPINonBit_Bool ();
   rule r;
      $display("F and F = %b",my_and(False, False));
      $display("F and T = %b",my_and(False, True ));
      $display("T and F = %b",my_and(True , False));
      $display("T and T = %b",my_and(True , True ));

      $display("F xor F = %b",my_xor(False, False));
      $display("F xor T = %b",my_xor(False, True ));
      $display("T xor F = %b",my_xor(True , False));
      $display("T xor T = %b",my_xor(True , True ));

      $finish(0);
   endrule
endmodule
