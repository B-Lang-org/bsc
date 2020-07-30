
(* synthesize *)
module sysRepeatedTask_OneRule() ;

   Reg#(Bool) b <- mkReg(True);

   function ActionValue#(Bit#(64)) adjusted_time();
   actionvalue
     let t <- $time;
     if (genVerilog)
       return (t + 5);
     else
       return t;
   endactionvalue
   endfunction

   rule r1 ( b ) ;
      $display("d1 %d", adjusted_time()) ;
      $display("d2 %d", adjusted_time()) ;
      b <= False ;
   endrule

   rule r2 ( !b ) ;
      $finish(0) ;
   endrule
   
endmodule

