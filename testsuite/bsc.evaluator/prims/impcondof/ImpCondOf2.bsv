function String showBool(Bool b);
   return (b ? "True" : "False");
endfunction

(* synthesize *)
module sysImpCondOf2();
   
   Reg#(Bool) b <- mkReg(False);
   
   Reg#(UInt#(14)) count <- mkReg(0);
   
   Integer x = when(count == 2, 2);
   Integer y = when(count == 0, 0);
   
   Integer z = b ? x : y;
   
   Bool cond = impCondOf(z);
   
   rule test;
      $display("Count: %0d", count, " b: ", showBool(b));
      $display("Condition: ", showBool(cond));
      
      b <= !b;
      if (count < 2) count <= count + 1;
      if(count == 2 && b) $finish(0);
   endrule

endmodule
 
