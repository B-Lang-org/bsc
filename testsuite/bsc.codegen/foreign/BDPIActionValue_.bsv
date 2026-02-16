import "BDPI" function ActionValue_#(Bit#(32)) my_time (Bit#(8) x);

function ActionValue#(Bit#(32)) my_time2(Bit#(8) x);
   let y = my_time(x);
   return fromActionValue_(y);
endfunction

(* synthesize *)
module mkBDPIActionValue_ ();
   rule r;
      let a <- my_time2(0);
      $display("%d",a);
      $finish(0);
   endrule
endmodule
