
// Range for Int 6 is -32 to 31

//typedef Bit#(5) BT ;
typedef Int#(6) BT ;

(* synthesize *)
module mkintok();

   BT foo = fromInteger(-33) ;
   
   Reg#(BT) t1 <- mkReg(31) ;
   rule foor (True ) ;
      t1 <= t1 + foo ;
   endrule
   
endmodule
