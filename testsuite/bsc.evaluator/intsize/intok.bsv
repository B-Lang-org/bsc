
// Range for Int 6 is -32 to 31

//typedef Bit#(5) BT ;
typedef Int#(6) BT ;

(* synthesize *)
module mkintok();

   BT foo = fromInteger(-32) ;
   
   Reg#(BT) t1 <- mkReg(31) ;
   rule foor ( t1 <= 4 ) ;
      t1 <= t1 + foo ;
   endrule

   rule foor2 ( t1 > 4 ) ;
      t1 <= fromInteger ( -32 ) ; // OK
//      t1 <= minBound ;          // OK
//      t1 <= -32 ; // NO good
//      t1 <= -31 ; // OK
//      t1 <= - ( 32 ) ;// NO good
//      t1 <= - fromInteger(32) ;// NO good
//      t1 <= truncate( 0 - 32 ) ;// NO good,   should work in verilog
//      t1 <= truncate( 32'd0 - 32 ) ;// OK
//      t1 <= 6'h3f ;             // OK
//      t1 <= - 6'h3f ;           // OK  give 6'd1 !
   endrule
   
endmodule
