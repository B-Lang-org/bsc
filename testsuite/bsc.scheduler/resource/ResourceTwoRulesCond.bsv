import RegFile::*;
import Vector::*;

// make sure conditions on method uses don't break the resource scheduler
(* synthesize *)
module sysResourceTwoRulesCond();
   
   RegFile#(UInt#(3), Bit#(32)) rf <- mkRegFileFull;
   
   Vector#(8, Reg#(Bit#(32))) dest <- replicateM(mkRegU);
   
   Vector#(8, Reg#(Bool)) do_write <- replicateM(mkRegU);

   for (Integer i = 0; i < 8; i = i + 1) begin
      rule contend;
	 if (do_write[i]) dest[i] <= rf.sub(fromInteger(i));
      endrule
   end
   
endmodule


   
