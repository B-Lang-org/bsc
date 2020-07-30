
// The generated code should not have these lines:
//
//    if (!1'd1) i_r0 <= 32'd0;
//
//    (negedge 1'd1)
//    if (!1'd1) i_r2
//

(* synthesize *)
module mkTestNoReset() ;

   Reg#(int)  r0() ;
   mkReg#(0) i_r0( r0, reset_by noReset ) ;


   Reg#(int)  r2() ;
   mkRegA#(0) i_r2( r2, reset_by noReset ) ;

   Reg#(int)  r1 <- mkReg( 3 ) ;

   rule rule1 ( True ) ;
      $display( "regs are %d %d", r0, r1 ) ;
   endrule
      
endmodule


module mkTestSub( Reg#(int) ) ;

   Reg#(int)  r0() ;
   mkReg#(0) i_r0( r0 ) ;
   Reg#(int)  r1 <- mkReg( 3 ) ;
   Reg#(int)  r2 <- mkRegA( 4 ) ;

   rule rule1 ( True ) ;
      $display( "regs are %d %d", r0, r1 ) ;
   endrule

   return r1 ;
endmodule

// Here is another example of optimizations which occur

(* synthesize *)
module mkTestSubTop( ) ;

   Reg#(int) sub() ;
   mkTestSub isub( sub, reset_by noReset ) ;

   rule rule1 ( True ) ;
      $display( "regs are %d", sub ) ;
   endrule

endmodule

