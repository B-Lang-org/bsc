import Vector::*;
import SatMath::*;

(* synthesize *)
module mkSatTest();
   Reg#(UInt#(8)) val <- mkReg(0);
   
   rule count;
      if (val == 255) $finish(0);
      val <= val + 1;
   endrule: count
   
   rule show;
      UInt#(2) how_many = fold(addSat(2), map(boolToSat, bitsToVector(val)));
      case (how_many)
	 0: $display("val %h has no set bits", val);
	 1: $display("val %h has one bit set", val);
	 2: $display("val %h has more than one bit set", val);
      endcase
   endrule: show
   
endmodule
