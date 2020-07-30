function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

(* synthesize *)
module sysAVCond();
   
   Reg#(Bool) a_cond <- mkReg(True);
   Reg#(Bool) v_cond <- mkReg(True);

   Integer v = when(v_cond,1);
   Action  a = when(a_cond, $display("Test"));

   let av = actionvalue a; return(v); endactionvalue;
   
   Bool cond = impCondOf(av);
   
   rule flip;
      a_cond <= !a_cond;
      if(!a_cond) v_cond <= !v_cond;
   endrule
   
   rule check;
      $display("Cond: ", showBool(cond));
      if(!a_cond && !v_cond) $finish(0);
   endrule
   
endmodule

