interface Sub;
   method Bool get (Bit#(2) key);
endinterface

(* synthesize *)
module mkAVMuxSub (Sub);
   method Bool get (Bit#(2) key);
      return (key == 2);
   endmethod
endmodule


interface Foo;
   method ActionValue#(Bool) f();
   method ActionValue#(Bool) g();
endinterface

(* synthesize *)
(* always_ready *)
module mkAVMuxTop (Foo);
   Reg#(Bit#(2)) x <- mkRegU;
   Reg#(Bit#(2)) y <- mkRegU;

   Sub s <- mkAVMuxSub;

   method ActionValue#(Bool) f ();
      x <= x + 1;
      return (s.get(y));
   endmethod

   method ActionValue#(Bool) g ();
      x <= x + 2;
      return (s.get(x));
   endmethod
endmodule

