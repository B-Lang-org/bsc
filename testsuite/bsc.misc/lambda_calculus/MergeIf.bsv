import FIFOF::*;


typedef Int#(17) XXX;

(* synthesize*)
module sysMergeIf ();
   Reg#(XXX) a <- mkReg(0);
   Reg#(XXX) b <- mkReg(5);
   Reg#(XXX) c <- mkReg(5);

   Reg#(Bool) s1 <- mkReg(False);
   Reg#(Bool) s2 <- mkReg(False);
   Reg#(Bool) s3 <- mkReg(False);
   
   FIFOF#(XXX) f1 <- mkFIFOF;
   FIFOF#(XXX) f2 <- mkFIFOF;
   FIFOF#(XXX) f3 <- mkFIFOF;
   
   rule r1 (True);
      if (s1) begin
         a <= 5;
         f2.enq(13);
      end
      if (s1) begin
         b <= 6;
      end
      else begin
         c <= 7;
      end
      
      if (!s1) begin
         f1.enq(12);
      end
      
      f3.enq(22);
   endrule
   
endmodule
