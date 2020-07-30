import List::*;

function String showBool(Bool b);
   return (b ? "True" : "False");
endfunction

(* synthesize *)
module sysListCond();
   
   Reg#(Bit#(2)) count <- mkReg(0);
   
   Bool a = count[0] == 1;
   Bool b = count[1] == 1;
   
   Integer i = when(b,1);
   Integer j = 5;
   Integer k = when(a,7);
   
   List#(Integer) l = cons(i,cons(j,cons(k,nil)));
  
   Bool cond = impCondOf(l);
   
   rule test;
      $display("Cond: ", showBool(cond));
      if (count == 3) $finish(0);
      count <= count + 1;
   endrule
   
endmodule

