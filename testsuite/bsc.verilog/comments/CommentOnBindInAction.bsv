(* synthesize *)
module mkCommentOnBindInAction();
   Reg#(Bool) r <- mkRegU;
   IFC i <- mkSub;

   rule do_something;
      (* doc = "Can we document this?" *)
      let v <- i.get;
      r <= v;
   endrule
   
endmodule

interface IFC;
   method ActionValue#(Bool) get;
endinterface

module mkSub(IFC);
   Reg#(Bool) x <- mkRegU;
   method ActionValue#(Bool) get();
      x <= !x;
      return x;
   endmethod
endmodule

