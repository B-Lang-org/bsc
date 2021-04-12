
import GetPut :: *;

typedef Bit #(0)  T;

(* synthesize *)
module mkZeroBitActionValueMethod_Get (Get#(T));
endmodule

(* synthesize *)
module mkZeroBitActionValueMethod_Put (Put#(T));
endmodule

(* synthesize *)
module sysZeroBitActionValueMethod ();

   Get#(T) g <- mkZeroBitActionValueMethod_Get;
   Put#(T) p <- mkZeroBitActionValueMethod_Put;

   rule connect;
      let v <- g.get;
      p.put(v);
   endrule

endmodule

