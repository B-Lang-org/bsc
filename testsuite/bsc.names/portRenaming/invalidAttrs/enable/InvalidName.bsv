
interface Ifc;
 (* enable = "new&name" *)
 method Action check ();
endinterface

(* synthesize *) 
module mkInvalidName (Ifc);
endmodule
