function String showBool(Bool b);
   return (b ? "True" : "False");
endfunction

(* synthesize *)
module sysTupleCond();
   
   Reg#(Bit#(2)) count <- mkReg(0);
   
   Bool a = count[0] == 1;
   Bool b = count[1] == 1;
   
   Integer i = when(b,1);
   Bit#(5) x = when(a,5);
   
   Tuple2#(Integer,Bit#(5)) t = tuple2(i,x);
   
   Bool cond = impCondOf(t);
   
   rule test;
      $display("Cond: ", showBool(cond));
      if (count == 3) $finish(0);
      count <= count + 1;
   endrule
   
endmodule

