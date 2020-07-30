
// Template BSV file.
// The following 2 variable must be defined
//`define size 2
//`define modName mkTest


import FIFOF::*;

(* synthesize *)
module `modName ( );
   
   FIFOF#(Maybe#(Bit#(6))) fifo<- mkUGSizedFIFOF(`size);
   FIFOF#(void)   zfifo <- mkUGSizedFIFOF(`size ) ;
   
   Reg#(Bit#(6)) cnt <- mkReg(0);	

   rule push  ( True );
      if (cnt <= `size || cnt == 16 )
	 begin
	    fifo.enq(tagged Valid cnt);
            zfifo.enq(?) ;
	    $display($time," data enqued %0d", cnt );
	 end
      else if ( cnt > 8 && cnt < 16 )
         begin
	    $display($time, " out data = %0d, Valid is %0d, Empty:%0d", 
                     validValue(fifo.first), isValid(fifo.first) , fifo.notEmpty );
	    fifo.deq;
            zfifo.deq ;
         end
      else
	 begin
	    $display($time, " DEQ and ENQ, %0d  out data = %0d, Valid is %d, Empty:%d",
                     cnt,
                     validValue(fifo.first), isValid(fifo.first) , fifo.notEmpty );
	    fifo.deq;
            zfifo.deq ;

            zfifo.enq(?) ;
	    fifo.enq(tagged Valid cnt);
	 end
   endrule

   rule check_fifo_statsE ( fifo.notEmpty != zfifo.notEmpty ) ;
      $display( "Error: Empty status do not match: zfifo: %0d, fifo: %0d",
               zfifo.notEmpty, fifo.notEmpty ) ;
   endrule

   rule check_fifo_statsF ( fifo.notFull != zfifo.notFull ) ;
      $display( "Error: Full status do not match: zfifo: %0d, fifo: %0d",
               zfifo.notFull, fifo.notFull ) ;
   endrule
   
   rule fin_fl(cnt == 31);
      $finish(0);
   endrule
   
   rule inc;
      cnt <= cnt + 1;
   endrule
   
endmodule
