// This example comes from GitHub Issue #742

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
