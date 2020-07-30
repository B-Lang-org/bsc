// Should give type error, since argument to fwrite is not a File

(* synthesize *)
module sysFileTypeErr1 () ;
   
   Reg#(int) cnt <- mkReg(0);
   Reg#(File) fh <- mkReg(InvalidFile) ;
   
   rule open (cnt == 0 ) ;
      $display("opening file" ) ;
      let lfh <- $fopen("foo.out", "w" ) ;
      if ( lfh == InvalidFile )
         begin
            $display("cannot open foo.out");
            $finish(0);
         end
      cnt <= 1 ;
      fh <= lfh ;
   endrule
   
   rule dump (cnt > 0 );
      $display("writing to file %0d", cnt ) ;
      $fwrite( "ff", fh, "cnt = %0d\n", cnt);
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 15);
      $finish(0);
   endrule
   
endmodule
