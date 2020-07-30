// This test is based on a bug which Don baltus sent to eng on or about 17 April 2006
// It is not related to bug 810 except that is uses strings.


(* synthesize *)
module sysOpt_bug ();
   Reg#(Bit#(2)) cond <- mkReg(0);
   Reg#(int)  c <- mkReg(0) ;
   Reg#(Bit#(4)) x <- mkReg(0) ;
   
   RWire#(Bit#(2))  rw <- mkRWire ;

   rule r ( c > 1);
      
      Bit#(4) foo = 0 ; 
      case (fromMaybe(0,rw.wget))
         0: foo = 1;
         1: foo = 3;
         2: foo = 4;
         3: foo = 7;
      endcase
//      x <= foo ;
      $display( "The value1 is %d", foo );
   endrule
   rule incc ;
      c <= c + 1 ;
      cond <=  cond + 1 ;
      if ( c > 5 ) $finish(0) ;
   endrule
endmodule
