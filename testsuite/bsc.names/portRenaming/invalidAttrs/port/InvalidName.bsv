
interface Ifc;
 (* prefix="" *)
 method Action check ((* port="new&name" *)Bool x);
endinterface

(* synthesize *) 
module mkInvalidName (Ifc);
endmodule
