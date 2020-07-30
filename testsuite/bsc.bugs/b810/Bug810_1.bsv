(* synthesize *)
module sysBug810_1 ();
   Reg#(Bool) cond <- mkReg(True);
   Reg#(int)  c <- mkReg(0) ;
   rule r;
      String foo = cond ? "ST" : "LoaD" ;
      $display( "String is %s", foo ) ;
   endrule
   rule incc ;
      c <= c + 1 ;
      cond <= ! cond ;
      if ( c > 5 ) $finish(0) ;
   endrule
endmodule
