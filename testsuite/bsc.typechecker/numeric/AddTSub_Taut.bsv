interface Ifc#(numeric type x, numeric type y);
endinterface

module mkFoo (Ifc#(tot, part));
   Reg#(Bit#(tot)) rtot <- mkRegU;
   Reg#(Bit#(part)) rpart <- mkRegU;

   rule r;
      Bit#(TSub#(tot,part)) other_part = truncate(rtot);
      rtot <= {rpart, ~other_part};
   endrule
endmodule

