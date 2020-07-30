import Clocks :: * ;

// Clock periods
Integer p0 = 10;
Integer p1 = 20;
Integer p2 = 200;

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
module sysRstTest() ;
   // instantaite 2 clocks
   Reg#(Bit#(32)) cntr <- mkReg( 0 ) ;

   Clock clk1 <-  mkAbsoluteClock( 15, p1 ) ;
   Clock clk2 <-  mkAbsoluteClock( 100, p2 ) ;

   // Generate some reset sync for the clock
   Reset rst1  <- mkSyncResetFromCR(2, clk1 ) ;
   Reset rst2  <- mkSyncReset(2, rst1, clk2 ) ;

   MakeResetIfc spuriousReset <- mkReset(1, False, clk2 ) ;
   Reset rst2A = spuriousReset.new_rst ;

   Reg#(int)  x_clk1 <- mkReg(0, clocked_by clk1, reset_by rst2 ) ;
   Reg#(int)  x_clk2 <- mkReg(0, clocked_by clk2, reset_by rst2 ) ;
   Reg#(int)  x_clk2A <- mkReg(0, clocked_by clk2, reset_by rst2A ) ;

   rule dispReset( spuriousReset.isAsserted ) ;
      $display("spurious reset has been asserted %d", adj_stime(p0)) ;
   endrule
   
   rule c0 (True) ;
      if ( cntr == 0 )
	 $display( "cntr has come out of reset: %d", adj_stime(p0)) ;
      $display( "rul c0: %d,  %0d", adj_stime(p0), cntr );
      let next_cntr = cntr + 1;
      cntr <= next_cntr ;
      if (next_cntr[7:0] == 8'd125)
	 spuriousReset.assertReset;
   endrule

   rule c1 (True) ;
      if ( x_clk1 == 0 )
	 $display( "x_clk1 has come out of reset: %d", adj_stime(p1)) ;
      $display( "rul c1: %d,  %0d", adj_stime(p1), x_clk1 );
      x_clk1 <= x_clk1 + 1 ;
   endrule

   rule c2 (True) ;
      if ( x_clk2 == 0 )
	 $display( "x_clk2 has come out of reset: %d", adj_stime(p2)) ;
      $display( "rul c2: %d,  %0d", adj_stime(p2), x_clk2 );
      x_clk2 <= x_clk2 + 1 ;
      if ( x_clk2 > 20 ) $finish(0) ;
   endrule

   rule c2A (True) ;
      if ( x_clk2A == 0 )
	 $display( "x_clk2A has come out of reset: %d", adj_stime(p2)) ;
      $display( "rul c2A: %d,  %0d", adj_stime(p2), x_clk2A );
      x_clk2A <= x_clk2A + 1 ;
   endrule
   
   
endmodule

