
typedef enum { Start, R1, Done } State deriving (Eq, Bits);

(* synthesize *)
module sysRepeatedTask_OneRule2() ;

   Reg#(State) s <- mkReg(Start);

   // put the File in a reg so that the function can take no arguments
   Reg#(File) fr <- mkRegU;
   
   function ActionValue#(Int#(32)) adjusted_fgetc();
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
      let f <- $fopen("data.txt","r");
      fr <= f;
      s <= R1;
   endrule

   rule r1 ( s == R1 ) ;
      $display("d1 %h", adjusted_fgetc()) ;
      $display("d2 %h", adjusted_fgetc()) ;
      s <= Done ;
   endrule

   rule done ( s == Done ) ;
      $finish(0) ;
   endrule
   
endmodule

