// This test is based on a bug which Don baltus sent to eng on or about 17 April 2006
// It is not related to bug 810 except that is uses strings.


(* synthesize *)
module sysBug810_3 ();
   Reg#(Bit#(2)) cond <- mkReg(0);
   Reg#(int)  c <- mkReg(0) ;

   rule r ( c > 1);
      
      String foo = "default" ;
      case (cond)
         0: foo = "1" ;
         1: foo = "Is One";
         2: foo = "Bigger is 2";
         3: foo = "Yet a third string";
      endcase
      $display( "The string is %s", foo );
   endrule
   rule incc ;
      c <= c + 1 ;
      cond <=  cond + 1 ;
      if ( c > 5 ) $finish(0) ;
   endrule
endmodule
