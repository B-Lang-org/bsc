
interface Ifc;
 (* prefix="" *)
 method Action check ((* port="always" *)Bool x);
endinterface

(* synthesize *) 
module mkKeyword (Ifc);
endmodule
