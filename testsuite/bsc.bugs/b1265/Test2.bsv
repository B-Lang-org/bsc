import Vector :: *;

(* synthesize *)
module mkTest ();

   Reg#(Bit#(32)) addr <- mkRegU;

   let idx = (addr[31] == 1) ? 1 : 0;
   // these work:
   //let idx = addr[31];
   //bit idx = (addr[31] == 1) ? 1 : 0;

   Vector#(2,Reg#(Bool)) vSel  <- replicateM(mkRegU);

   rule genSel ;
      vSel[idx] <= True;
   endrule

endmodule

