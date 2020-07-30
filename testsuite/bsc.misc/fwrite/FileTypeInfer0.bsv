// Test to see that the type for fh is inferred to be File
// even if File is never specified

(* synthesize *)
module sysFileTypeInfer0 () ;
   
   Reg#(int) cnt <- mkReg(0);
   let fh <- mkRegU ;
   
   rule open (cnt == 0 ) ;
      $display("opening file" ) ;
      //let lfh <- $fopen("foo.out", "w" ) ;
      let lfh = ? ;
      cnt <= 1 ;
      fh <= lfh ;
   endrule
   
   rule dump (cnt > 0 );
      $display("writing to file %0d", cnt ) ;
      $fwrite( fh, "cnt = %0d\n", cnt);
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 15);
      $finish(0);
   endrule
   
endmodule
