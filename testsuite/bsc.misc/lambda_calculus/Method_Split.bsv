interface Ifc;
   method ActionValue#(Bit#(8)) m();
endinterface

(* synthesize *)
module sysMethod_Split(Ifc);

   Reg#(Bit#(8)) rg1 <- mkRegU;
   Reg#(Bit#(8)) rg2 <- mkRegU;

   Reg#(Bool) c <- mkRegU;

   method ActionValue#(Bit#(8)) m();
      (* split *)
      if (c) begin
         rg1 <= rg1 + 3;
         return (rg1 + 1);
      end
      else begin
         rg2 <= rg2 + 4;
         return (rg2 + 2);
      end
   endmethod

endmodule

