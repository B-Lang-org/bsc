function String showBool(Bool b);
   return (b ? "True" : "False");
endfunction

(* synthesize *)
module sysMaybeCond();
   
   Reg#(Bit#(2)) count <- mkReg(0);
   
   Bool a = count[0] == 1;
   Bool b = count[1] == 1;
   
   Integer i = when(b,1);
   
   Maybe#(Integer) mi = a ? tagged Invalid : tagged Valid i;
   
   Bool cond = impCondOf(mi);
   
   rule test;
      $display("Cond: ", showBool(cond));
      if (count == 3) $finish(0);
      count <= count + 1;
   endrule
   
endmodule

