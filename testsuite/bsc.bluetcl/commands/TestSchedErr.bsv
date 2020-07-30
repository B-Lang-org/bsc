// An example with an error in the scheduling stage
// (to test the reporting of partial scheduling info)

// The error here is a rule that calls two methods that cannot execute in
// parallel.  This occurs after the required fields are computed (method uses)
// but before any optional fields are computed (the next being the RAT).

(* synthesize *)
module mkTestSchedErr();
   Reg#(Bit#(8)) rg <- mkRegU;

   rule r1;
      rg <= 0;
      rg <= 1;
   endrule
endmodule

