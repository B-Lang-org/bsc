function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

(* synthesize *)
module sysWireCond();
   
   Wire#(Bit#(32)) w <- mkWire;
   
   Bool cond = impCondOf(w);
   
   Reg#(Bool) flip <- mkReg(False);
   
   rule drive_wire(flip);
      w <= 5;
   endrule

   rule toggle;
      flip <= !flip;
   endrule
   
   rule test_cond;
      $display("Cond: ", showBool(cond));
      if(flip) $finish(0);
   endrule

endmodule

   
