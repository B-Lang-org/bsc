
import "BDPI" function ActionValue#(Bit#(0)) my_time (Bit#(8) x);

(* synthesize *)
module sysZeroBitActionValueForeignWithArgs ();

   rule do_disp;
      let v <- my_time(0);
      $display("v = %b", v);
   endrule

endmodule

