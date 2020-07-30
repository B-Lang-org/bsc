// This defaults to Star kind
typeclass A#(type a, type b);
endtypeclass

instance A#(a,a);
endinstance

module mkDefaultProvisoMismatch_TyCon()
   provisos (A#(TLog#(35), sz));

   Reg#(Bit#(sz)) r <- mkRegU;
endmodule
