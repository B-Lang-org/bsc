
import FIFO::*;
import Vector::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 4   SIZE;

(*synthesize, options ="-elab"*)
module sysLoopSkip ();
   
   Reg#(I) aaa, bbb;
   for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin
      if (i %2 == 0) begin
         aaa <- mkRegU;
      end
      else begin
         bbb <- mkRegU;
         aaa = asIfc(bbb);
      end
      rule foo (True);
         $display(aaa);
      endrule
   end
   
   for (Integer i = 0; i < valueOf(SIZE) ; i = i + 1) begin: foo
      bbb <- mkRegU;
   end
   
endmodule
