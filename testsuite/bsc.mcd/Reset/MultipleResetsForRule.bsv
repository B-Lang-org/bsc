import Clocks :: * ;

// Clock periods
Integer p1 = 10;

// function to make $stime the same for Bluesim and Verilog
function ActionValue#(Bit#(32)) adj_stime(Integer p);
   actionvalue
      let adj = (p + 1) / 2;
      let t <- $stime();
      if (genVerilog)
	 return (t + fromInteger(adj));
      else
	 return t;
   endactionvalue
endfunction

(* synthesize *) 
module sysMultipleResetsForRule() ;

   Reset rst0 <- exposeCurrentReset ;
   Reset rst1 <- mkInitialReset( 3 ) ;

   Reg#(int) x0 <- mkReg( 0, reset_by rst0 ) ;
   Reg#(int) x1 <- mkReg( 0, reset_by rst1 ) ;

   rule r1 ;
      $display( "rule r1" );
      $display( "rule r1: (%d) %d %d", adj_stime(p1), x0, x1 );
      x0 <= x0 + 1;
      x1 <= x1 + 2;
      if (x0 > 7)
	 $finish(0);
   endrule
   
endmodule

