
typedef enum { Start, R1, Display, Done } State deriving (Eq, Bits);

typedef Int#(32) DataT;

(* synthesize *)
module sysRepeatedTask_OneRule3() ;

   Reg#(State) s <- mkReg(Start);

   Reg#(DataT) rg1 <- mkReg(0);
   Reg#(DataT) rg2 <- mkReg(0);

   // put the File in a reg so that the function can take no arguments
   Reg#(File) fr <- mkRegU;
   
   function ActionValue#(DataT) adjusted_fgetc();
      actionvalue
	 let i <- $fgetc(fr);
	 // use a case-statement to prevent inlining
	 case (i)
	    -1 : return -1;
	    1  : return 2;
	    2  : return 1;
	    default : return (i + 2);
	 endcase
      endactionvalue
   endfunction

   rule start ( s == Start ) ;
      let f <- $fopen("data.txt","r") ;
      fr <= f ;
      s <= R1 ;
   endrule

   rule r1 ( s == R1 ) ;
      let v1 <- adjusted_fgetc() ;
      rg1 <= v1;
      let v2 <- adjusted_fgetc() ;
      rg2 <= v2;
      s <= Display ;
   endrule

   rule disp ( s == Display ) ;
      $display("rg1 = %h", rg1) ;
      $display("rg2 = %h", rg2) ;
      s <= Done ;
   endrule

   rule done ( s == Done ) ;
      $finish(0) ;
   endrule
   
endmodule

