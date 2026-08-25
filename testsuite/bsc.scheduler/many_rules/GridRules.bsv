// An 8x8 torus of tiles, each with one accumulator register and one
// rule per direction reading a neighbor's accumulator and writing its
// own -- the "tile grid" shape of real designs: interaction is local
// and constant-degree (a rule shares state only with its tile-mates
// and the rules reading its tile), while the rule-pair space grows
// quadratically.  The accumulators are ConfigRegs, whose read and
// write do not impose an execution order, so the toroidal dataflow
// does not create ordering cycles.  The expected schedule dump locks
// the blocker structure, urgency choices, and warnings for this
// topology.
import Vector::*;
import ConfigReg::*;

(* synthesize *)
module mkGridRules(Empty);
  Vector#(64, Reg#(UInt#(16))) acc <- replicateM(mkConfigReg(0));
  for (Integer i = 0; i < 8; i = i + 1)
    for (Integer j = 0; j < 8; j = j + 1) begin
      Integer t = i * 8 + j;
      Integer north = ((i + 7) % 8) * 8 + j;
      Integer south = ((i + 1) % 8) * 8 + j;
      Integer west  = i * 8 + ((j + 7) % 8);
      Integer east  = i * 8 + ((j + 1) % 8);
      rule flow_n; acc[t] <= acc[t] + acc[north]; endrule
      rule flow_s; acc[t] <= acc[t] + acc[south]; endrule
      rule flow_w; acc[t] <= acc[t] + acc[west];  endrule
      rule flow_e; acc[t] <= acc[t] + acc[east];  endrule
    end
endmodule
