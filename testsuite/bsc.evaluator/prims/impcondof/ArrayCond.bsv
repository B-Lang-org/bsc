import Vector::*;

function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

(* synthesize *)
module sysArrayCond();
   
   Reg#(Bool) a <- mkReg(True);
   Reg#(Bool) b <- mkReg(True);
   
   Vector#(2,Integer) vs;
   vs[0] = when(a,1);
   vs[1] = when(b,2);
   
   Bool cond = impCondOf(vs);
   
   rule flip;
      a <= !a;
      if(!a) b <= !b;
   endrule
   
   rule check;
      $display("Cond: ", showBool(cond));
      if(!a && !b) $finish(0);
   endrule
   
endmodule

