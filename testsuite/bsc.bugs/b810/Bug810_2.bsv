(* synthesize *)
module sysBug810_2 ();
   Reg#(Bool) cond <- mkReg(True);
   Reg#(int)  c <- mkReg(0) ;
   Reg#(String) sr <- mkRegU ; // ("Empty" ) ;
   rule r ( c > 1);
      String foo = cond ? "ST" : "LoaD" ;
      sr <= foo ;
   endrule
   rule incc ;
      c <= c + 1 ;
      cond <= ! cond ;
      if ( c > 5 ) $finish(0) ;
   endrule
endmodule
