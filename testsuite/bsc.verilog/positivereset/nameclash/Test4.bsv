interface Ifc;
endinterface


(*synthesize*)
(*reset_prefix = "RESET_P" *)
module sysTest4 (Ifc);
   Reg#(UInt#(9)) c <- mkReg(0);
   rule fine (True);
      $display ("final rule %d", c);
      $finish(0);
   endrule
endmodule
