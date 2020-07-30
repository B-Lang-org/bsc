
typedef enum { R1, R2, Done } State deriving (Eq, Bits);

(* synthesize *)
module sysRepeatedTask_TwoRules() ;

   Reg#(State) s <- mkReg(R1);
   
   function ActionValue#(Bit#(64)) adjusted_time();
   actionvalue
     let t <- $time;
     if (genVerilog)
       return (t + 5);
     else
       return t;
   endactionvalue
   endfunction

   rule r1 ( s == R1 ) ;
      $display("r1 %d", adjusted_time()) ;
      s <= R2 ;
   endrule

   rule r2 ( s == R2 ) ;
      $display("r2 %d" , adjusted_time()) ;
      s <= Done ;
   endrule

   rule r3 ( s == Done ) ;
      $finish(0);
   endrule

endmodule

