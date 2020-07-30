// create a module with an input port
(* synthesize *)
module mkOptAcrossRWireInInst_Sub #(Bool x) ();
endmodule

(* synthesize *)
module sysOptAcrossRWireInInst (Empty);
   Reg#(Bool) x <- mkRegU;
   
   RWire#(Bool) rw <- mkRWire;
   let w = fromMaybe(False, rw.wget());
   
   Empty foo <- mkOptAcrossRWireInInst_Sub(w || x);

   rule rule1;
      rw.wset(x);
   endrule

endmodule


