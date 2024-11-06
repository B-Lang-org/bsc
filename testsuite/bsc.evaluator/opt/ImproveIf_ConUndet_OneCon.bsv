// This example comes from GitHub Issue #742
//
// This is a simple example that should compile without a lot of
// unfolding steps or heap space.  However, if the evaluator is
// missing an optimization for this:
//
//     if (cond)
//       then Ctor e1 e2 ...
//       else _
//
// the compiler will take time and memory until eventually exiting
// with an error message about max unfolding steps reached or
// (if the max steps is increased) that stack space was exhausted.
//
// For better code generation of "pack of unpack" for union types, we
// don't want the evaluator to optimize away the don't-care like this:
//
//     ==> Ctor e1 e2 ...
//
// However, when the type only has one constructor, such as Vector in
// this example, we can optimize the expression to this:
//
//     ==> Ctor
//           (if (cond) then e1 else _)
//           (if (cond) then e2 else _)
//           ...
//
// With this optimization, the example will successfully compile
// (quickly, without many unfolding steps or stack space usage).
//

import Vector::*;

`define Q_SIZE 8
typedef Bit#(2) T;

(*synthesize*)
module mkImproveIf_ConUndet_OneCon ();

  Vector#(`Q_SIZE, Reg#(T))           vec_data  <- replicateM(mkRegU);
  Reg #(Maybe#(Vector#(`Q_SIZE, T)))  rg_1   <- mkRegU;
  Reg #(Maybe#(Vector#(`Q_SIZE, T)))  rg_2   <- mkRegU;
  Reg #(Vector#(`Q_SIZE, Bool))       rg_3   <- mkRegU;
  Reg #(Maybe#(Vector#(`Q_SIZE, T)))  rg_4   <- mkRegU;
  Reg #(Vector#(`Q_SIZE, Bool))       rg_5   <- mkRegU;

  rule r;
    Vector#(`Q_SIZE, T) tmp_data = readVReg (vec_data);

    if (rg_1 matches tagged Valid .d1)
      tmp_data  = d1;

    if (rg_2 matches tagged Valid .d2)
      begin
        for (int i = 0 ; i< `Q_SIZE ;i = i+1)
          begin
            if (rg_3[i] == True)
              tmp_data[i] = d2[i];
            end
      end

    if (rg_4 matches tagged Valid .d4)
      begin
        for (int i = 0 ; i< `Q_SIZE ;i = i+1)
          begin
            if (rg_5[i] == True)
              tmp_data[i] = d4[i];
          end
      end

    writeVReg(vec_data,tmp_data);
  endrule

endmodule
