
interface Ifc;
 (* ready = "new&name" *)
 method Bool check ();
endinterface

(* synthesize *) 
module mkInvalidName (Ifc);
endmodule
