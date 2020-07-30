import RegFile::*;
import Sub::*;

(* synthesize *)
module sysMethodConds_MultiplicityCond ();
   Ifc s <- mkUserSub;

   RegFile#(UInt#(5), Bool) rf <- mkRegFileFull;

   Reg#(UInt#(5)) idx1 <- mkReg(0);
   Reg#(UInt#(5)) idx2 <- mkReg(0);

   rule r1;
      Bool c = rf.sub(idx1);
      if (c) begin
         // there will be multiple COND signals assigned to the task result
         s.am1(0);
	 s.am2;
	 // and the task result is the condition of another task
	 $display("True");
      end
   endrule

   rule r2;
      Bool c = rf.sub(idx2);
      if (c) begin
         idx2 <= idx2+1;
      end
   endrule
endmodule

