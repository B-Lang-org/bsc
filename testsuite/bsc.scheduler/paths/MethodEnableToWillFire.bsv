interface IFC;
   method Action inp ();
   method Maybe#(Bool) result;
endinterface

(* synthesize *)
module mkMethodEnableToWillFire (IFC);
   Reg#(Bit#(8)) rg <- mkRegU;
   RWire#(Bool) rw <- mkRWire;

   rule r;
      rg <= rg + 1;
      rw.wset(rg[0]==1);
   endrule

   method result = rw.wget;

   method Action inp ();
      rg <= rg - 1;
   endmethod
endmodule

